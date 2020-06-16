#' ---
#' title: covid-tb
#' author: Philippe Glaziou
#' date: 02/05/2020 
#' output:
#'    html_document:
#'      mode: selfcontained
#'      toc: true
#'      toc_depth: 3
#'      toc_float: true
#'      number_sections: true
#'      theme: flatly
#'      highlight: zenburn
#'      df_print: paged
#'      code_folding: hide
#' ---

#' Last updated: 2020-06-16
#'
#'
#'
#' # Load libraries and data
#'
library(data.table)
library(ggplot2)
library(propagate)
library(imputeTS)
library(directlabels) # TODO: update code using ggrepel instead of directlabels 

load('Rdata/global.Rdata')
load('Rdata/regional.Rdata')
load('Rdata/pop.Rdata')
load('Rdata/est.Rdata')


#' # Functions
#' 

#' returns Beta shape and scale params using the method of moments
#'
get.beta <- function(ev, sd) {
  #' @param ev expected value.
  #' @param sd standard deviation.
  #' @export
  stopifnot(ev > 0 & ev < 1)
  stopifnot(sd > 0)
  
  S = (ev * (1 - ev) / sd ^ 2) - 1
  if (S < 0)
    stop('Not distributed Beta: sd^2 >= ev*(1-ev)')
  
  a = S * ev
  b = S * (1 - ev)
  return(c(a = a, b = b))
}

#' generate low and high bounds assuming Beta distribution
#'
lohi <- function(ev, sd) {
  #' @param ev expected value.
  #' @param sd standard deviation.
  #' @export 
  stopifnot(ev > 0 & ev < 1)
  stopifnot(sd > 0)
  
  par <- get.beta(ev, sd)
  lo <- qbeta(0.025, par[1], par[2])
  hi <- qbeta(0.975, par[1], par[2])
  return(c(lo = lo, hi = hi))
}


#' mortality from incidence
#' 
inc2mort <- function(inc,
                     inc.sd,
                     newinc,
                     tbhiv,
                     tbhiv.sd,
                     art = NA,
                     art0 = 0,
                     noHIV = TRUE)
{
  #' function to derive mortality from incidence
  #'
  #' @param inc incidence rate.
  #' @param inc.sd SD of incidence rate.
  #' @param newinc detection rate.
  #' @param tbhiv proportion HIV+.
  #' @param tbhiv.sd SD of proportion HIV+.
  #' @param art ART coverage in detected TB.
  #' @param art0 ART coverage in undetected TB.
  #' @param HIV-neg (noHIV=TRUE) or HIV-pos (noHIV=FALSE).
  #' @export
  require(propagate) # use second-order Taylor expansion about moments
  
  stopifnot(inc >= 0 & inc.sd >= 0)
  stopifnot(newinc >= 0)
  stopifnot((tbhiv >= 0 & tbhiv <= 1) | is.na(tbhiv))
  stopifnot((tbhiv.sd >= 0 & tbhiv.sd < 1) | is.na(tbhiv))
  stopifnot((art >= 0 & art <= 1) | is.na(art))
  stopifnot((art0 >= 0 & art0 <= 1) | is.na(art0))
  stopifnot(noHIV == TRUE | noHIV == FALSE)
  
  if (is.na(tbhiv))
    tbhiv <- 0
  if (is.na(tbhiv.sd))
    tbhiv.sd <- 0
  if (!noHIV)
    if (is.na(art))
      art <- 0
  if (!noHIV)
    if (is.na(art0))
      art0 <- 0
  if (inc < newinc)
    inc <- newinc
  
  # CFRs HIV-negative
  CFRu <- c(0.43, (0.53 - 0.28) / 3.92) # undetected
  CFRd <- c(0.03, 0.07 / 3.92)          # detected
  
  # CFRs HIV-positive
  # noART, untx 0.78 (0.65-0.94)
  CFR.noARTu <- c(0.78, (0.94 - 0.65) / 3.92)
  
  # noART, tx 0.09 (0.03-0.15)
  CFR.noARTd <- c(0.09, (0.15 - 0.03) / 3.92)
  
  # ART1, untx 0.62 (0.39-0.86) less than one year
  ART1.u.cfr <- 0.62
  ART1.u.cfr.sd <- (0.86 - 0.39) / 3.92
  
  # ART1, tx 0.06 (0.01-0.13)
  ART1.n.cfr <- 0.06
  ART1.n.cfr.sd <- (0.13 - 0.01) / 3.92
  
  # ART2, untx 0.49 (0.31-0.70) more than one year
  ART2.u.cfr <- 0.49
  ART2.u.cfr.sd <- (0.7 - 0.31) / 3.92
  
  # ART2, tx 0.04 (0.00-0.10)
  ART2.n.cfr <- 0.04
  ART2.n.cfr.sd <- 0.1 / 3.92
  
  # ART unknown duration, take unweighted average
  CFR.ARTu <-
    c(mean(ART1.u.cfr, ART2.u.cfr),
      mean(ART1.u.cfr.sd, ART2.u.cfr.sd))
  CFR.ARTd <-
    c(mean(ART1.n.cfr, ART2.n.cfr),
      mean(ART1.n.cfr.sd, ART2.n.cfr.sd))
  
  I <- c(inc, inc.sd)
  
  # split error about I between treated N and untreated U
  U <-
    c(max(inc - newinc, 0), inc.sd * max(inc - newinc, 0) / inc) # untreated
  N <- c(newinc, inc.sd * newinc / inc) # treated
  
  H <- c(tbhiv, tbhiv.sd)
  ARTd <- c(art, 0)
  ARTu <- c(art0, 0)
  
  if (noHIV) {
    DT <- cbind(CFRu, CFRd, U, H, N)
    EXPR <- expression((U * CFRu + N * CFRd) * (1 - H))
  } else {
    DT <-
      cbind(CFR.noARTu,
            CFR.noARTd,
            CFR.ARTu,
            CFR.ARTd,
            U,
            H,
            N,
            ARTd,
            ARTu)
    EXPR <- expression((
      U * (ARTu * CFR.ARTu + (1 - ARTu) * CFR.noARTu) +
        N * (ARTd * CFR.ARTd + (1 - ARTd) * CFR.noARTd)
    ) * H)
  }
  
  out <-
    propagate(
      expr = EXPR,
      data = DT,
      type = 'stat',
      do.sim = F,
      second.order = T
    )
  
  return(out)
}


#' model
#' 
covidtb <- function(dta, adj = 0, pop2020, dec=0.04) {
  vlohi <- Vectorize(lohi, c('ev', 'sd'))
  
  drop <- seq(0, .7, by = 0.05)
  dur <- seq(0, 8, by = .5) / 10
  
  proj <- data.table(expand.grid(dur, drop))
  setnames(proj, c('drop', 'dur'))
  
  proj <- cbind(
    proj,
    data.table(
      e.mort.nh = numeric(),
      e.mort.nh.sd = numeric(),
      e.mort.h = numeric(),
      e.mort.h.sd = numeric()
    )
  )
  
  for (i in 1:nrow(proj)) {
    out.nh <-
      dta[, {
        tmp = inc2mort(inc,
                       inc.sd,
                       newinc * (1 - proj$drop[i] * proj$dur[i]) / (1 - adj),
                       tbhiv,
                       tbhiv.sd,
                       noHIV =
                         T)$prop
        
        list(e.mort.nh = tmp[2] * (1 - dec),
             e.mort.nh.sd = tmp[4] * (1 - dec))
      }]
    out.h <-
      dta[, {
        tmp = inc2mort(inc,
                       inc.sd,
                       newinc * (1 - proj$drop[i] * proj$dur[i]),
                       tbhiv,
                       tbhiv.sd,
                       noHIV =
                         F)$prop
        
        list(e.mort.nh = tmp[2] * (1 - dec),
             e.mort.nh.sd = tmp[4] * (1 - dec))
      }]
    proj[i, (3:4) := out.nh]
    proj[i, (5:6) := out.h]
  }
  
  #' excess TB deaths
  #'
  proj[, mort := e.mort.nh + e.mort.h]
  proj[, mort.sd := sqrt(e.mort.nh.sd ^ 2 + e.mort.h.sd ^ 2)]
  out <- proj[, vlohi(mort / 1e5, mort.sd / 1e5)]
  proj[, mort.lo := out[1, ] * 1e5]
  proj[, mort.hi := out[2, ] * 1e5]
  
  proj[, em := mort - mort[1]]
  proj[, em.sd := sqrt(mort.sd ^ 2 - mort.sd[1] ^ 2)]
  out <- proj[em > 0, vlohi(em / 1e5, em.sd / 1e5)]
  proj[em > 0, em.lo := out[1, ] * 1e5]
  proj[em > 0, em.hi := out[2, ] * 1e5]
  
  proj[, excess := em * pop2020 / 1e5]
  proj[, excess.lo := em.lo * pop2020 / 1e5]
  proj[, excess.hi := em.hi * pop2020 / 1e5]
  
  proj[, mort.num := mort * pop2020 / 1e5]
  proj[, mort.lo.num := mort.lo * pop2020 / 1e5]
  proj[, mort.hi.num := mort.hi * pop2020 / 1e5]
  proj[, mort.nh.num := e.mort.nh * pop2020 / 1e5]
  proj[, mort.h.num := e.mort.h * pop2020 / 1e5]
  
  return(proj)
}



#' fit model to global data
#' 
pop2020 <- sum(pop$pop[pop$year == 2020])
glb <- global[year == 2018]


proj <- covidtb(glb, adj = .057, pop2020=pop2020, dec=0.04)
(proj[])

p <- ggplot(proj, aes(drop * 100, dur * 12)) +
  geom_raster(aes(fill = excess / 1e6), interpolate = TRUE) +
  geom_contour(aes(z = excess / 1e6, colour = ..level..), binwidth =
                 .1) +
  scale_fill_gradient(
    "Excess TB deaths\n(millions)",
    low = "white",
    high = "firebrick",
    breaks = seq(0, 1.2, by = .1)
  ) +
  scale_x_continuous(
    limits = c(0, 90),
    expand = c(0, 0),
    breaks = seq(0, 80, by = 10)
  ) +
  scale_y_continuous(limits = c(0, 7),
                     expand = c(0, 0),
                     breaks = 0:8) +
  ggtitle('Excess TB deaths (Millions)') +
  xlab('Decrease in case detection (%)') +
  ylab('Duration of perturbation (months)') +
  theme_classic() +
  theme(legend.position = "none",
        plot.title = element_text(hjust = .5, size = 11))
(direct.label(p, "bottom.pieces"))

ggsave(
  direct.label(p, "bottom.pieces"),
  file = 'output/excessMortality.pdf',
  width = 6,
  height = 6
)

pg <- ggplot_build(p)$data[[2]]
fit <- lm(level ~ x * y, data = pg)

#' predicted exceess TB deaths (HIV-neg) if CDR drops by 25% over 2 months
#'
(predict(fit, newdata = data.table(x = 25, y = 3)))



#' fit model to MAR
#' 
mar <-
  covidtb(est[iso3 == 'MAR' &
                year == 2018], adj = 0, pop2020 = pop$pop[pop$year == 2020 &
                                                            pop$iso3 == 'MAR'], dec = 0.045)
(mar[])
p <- ggplot(mar, aes(drop * 100, dur * 12)) +
  geom_raster(aes(fill = excess / 1e3), interpolate = TRUE) +
  geom_contour(aes(z = excess / 1e3, colour = ..level..), binwidth =
                 .5) +
  scale_fill_gradient(
    "Excess TB deaths\n(millions)",
    low = "white",
    high = "firebrick",
    breaks = seq(0, 1.2, by = .1)
  ) +
  scale_x_continuous(
    limits = c(0, 90),
    expand = c(0, 0),
    breaks = seq(0, 80, by = 10)
  ) +
  scale_y_continuous(limits = c(0, 7),
                     expand = c(0, 0),
                     breaks = 0:8) +
  ggtitle('Excess TB deaths (Thousands)') +
  xlab('Decrease in case detection (%)') +
  ylab('Duration of perturbation (months)') +
  theme_classic() +
  theme(legend.position = "none",
        plot.title = element_text(hjust = .5, size = 11))
(direct.label(p, "bottom.pieces"))

ggsave(
  direct.label(p, "bottom.pieces"),
  file = 'output/excessMortality_Morocco.pdf',
  width = 6,
  height = 6
)

pg <- ggplot_build(p)$data[[2]]
fit <- lm(level ~ x * y, data = pg)
(predict(fit, newdata = data.table(x = 25, y = 3)))



#' PAK
#' 
pak <-
  covidtb(est[iso3 == 'PAK' &
                year == 2018], adj = 0.274, pop2020 = pop$pop[pop$year == 2020 &
                                                                pop$iso3 == 'PAK'], dec = 0.069)
(pak[])

p <- ggplot(pak, aes(drop * 100, dur * 12)) +
  geom_raster(aes(fill = excess / 1e3), interpolate = TRUE) +
  geom_contour(aes(z = excess / 1e3, colour = ..level..), binwidth =
                 5) +
  scale_fill_gradient(
    "Excess TB deaths\n(millions)",
    low = "white",
    high = "firebrick",
    breaks = seq(0, 1.2, by = 0.1)
  ) +
  scale_x_continuous(
    limits = c(0, 90),
    expand = c(0, 0),
    breaks = seq(0, 80, by = 10)
  ) +
  scale_y_continuous(limits = c(0, 7),
                     expand = c(0, 0),
                     breaks = 0:8) +
  ggtitle('Excess TB deaths (Thousands)') +
  xlab('Decrease in case detection (%)') +
  ylab('Duration of perturbation (months)') +
  theme_classic() +
  theme(legend.position = "none",
        plot.title = element_text(hjust = .5, size = 11))
(direct.label(p, "bottom.pieces"))

ggsave(
  direct.label(p, "bottom.pieces"),
  file = 'output/excessMortality_Pakistan.pdf',
  width = 6,
  height = 6
)




#' fit to regional data (EMR)
#' 
emr <-
  covidtb(regional[g.whoregion == 'EMR' &
                     year == 2018], adj = 0.22, pop2020 = sum(pop$pop[pop$year == 2020 &
                                                                        pop$g.whoregion == 'EMR']), dec = 0.0925)
(emr[])

p <- ggplot(emr, aes(drop * 100, dur * 12)) +
  geom_raster(aes(fill = excess / 1e3), interpolate = TRUE) +
  geom_contour(aes(z = excess / 1e3, colour = ..level..), binwidth =
                 5) +
  scale_fill_gradient(
    "Excess TB deaths\n(millions)",
    low = "white",
    high = "firebrick",
    breaks = seq(0, 1.2, by = 0.1)
  ) +
  scale_x_continuous(
    limits = c(0, 90),
    expand = c(0, 0),
    breaks = seq(0, 80, by = 10)
  ) +
  scale_y_continuous(limits = c(0, 7),
                     expand = c(0, 0),
                     breaks = 0:8) +
  ggtitle('Excess TB deaths (Thousands)') +
  xlab('Decrease in case detection (%)') +
  ylab('Duration of perturbation (months)') +
  theme_classic() +
  theme(legend.position = "none",
        plot.title = element_text(hjust = .5, size = 11))
(direct.label(p, "bottom.pieces"))

ggsave(
  direct.label(p, "bottom.pieces"),
  file = 'output/excessMortality_EMR.pdf',
  width = 6,
  height = 6
)

(mar[drop==0.25][6, ])
(pak[drop==0.25][6, ])
(emr[drop==0.25][6, ])


#' BGD
#' 
bgd <-
  covidtb(est[iso3 == 'BGD' &
                year == 2018], adj = 0, pop2020 = pop$pop[pop$year == 2020 &
                                                            pop$iso3 == 'BGD'], dec = 0.2)
(bgd[])

p <- ggplot(bgd, aes(drop * 100, dur * 12)) +
  geom_raster(aes(fill = excess / 1e3), interpolate = TRUE) +
  geom_contour(aes(z = excess / 1e3, colour = ..level..), binwidth =
                 2) +
  scale_fill_gradient(
    "Excess TB deaths\n(millions)",
    low = "white",
    high = "firebrick",
    breaks = seq(0, 1.2, by = 0.1)
  ) +
  scale_x_continuous(
    limits = c(0, 90),
    expand = c(0, 0),
    breaks = seq(0, 80, by = 10)
  ) +
  scale_y_continuous(limits = c(0, 7),
                     expand = c(0, 0),
                     breaks = 0:8) +
  ggtitle('Excess TB deaths (Thousands)') +
  xlab('Decrease in case detection (%)') +
  ylab('Duration of perturbation (months)') +
  theme_classic() +
  theme(legend.position = "none",
        plot.title = element_text(hjust = .5, size = 11))
(direct.label(p, "bottom.pieces"))

ggsave(
  direct.label(p, "bottom.pieces"),
  file = 'output/excessMortality_Bangladesh.pdf',
  width = 6,
  height = 6
)

(bgd[drop==0.25][6, ])




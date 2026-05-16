library(lpSolve)
# Calculate bounds on counterfactual fairness from Berkeley admission data
#
# Here we just pick two out of six departments
#
# For each possible pair, we calculate the lower and upper bound
# In this way we found that alpha=C, beta=B is a good pair 
# This gives a fairly strong counterfactual unfairness
#
# beta = 1, alpha = 2
# m = 1, f = 2
#
# Then we calculate a more general bound (>= 2 departments) and apply it on all departments
# In that case, the conclusion is that the counterfactual unfairness bound is too loose to lead to a conclusion (it contains 0)
N_D.G <- apply(UCBAdmissions,c(2,3),sum)
p_D.G <- function(alpha,beta) {
	A <- matrix(0,2,2)
	A[2,2] <- N_D.G[2,alpha] / (N_D.G[2,alpha] + N_D.G[2,beta])
	A[1,1] <- N_D.G[1,beta] / (N_D.G[1,alpha] + N_D.G[1,beta])
	A[1,2] <- N_D.G[2,beta] / (N_D.G[2,alpha] + N_D.G[2,beta])
	A[2,1] <- N_D.G[1,alpha] / (N_D.G[1,alpha] + N_D.G[1,beta])
	A
}
ub <- function(alpha,beta) { # upper bound for rho_{00}
	min(p_D.G(alpha,beta)[2,2],p_D.G(alpha,beta)[1,1]) / p_D.G(alpha,beta)[2,2]
}
lb <- function(alpha,beta) { # lower bound for rho_{00}
	1 - min(p_D.G(alpha,beta)[2,2],p_D.G(alpha,beta)[2,1]) / p_D.G(alpha,beta)[2,2]
}
lpf <- function(p) {
  f <- list(
    obj=c(0, 0, 1, 0),
    con=matrix(c(1, 0, 1, 0,
                 0, 1, 0, 1,
                 1, 1, 0, 0,
                 0, 0, 1, 1), nrow = 4, byrow = TRUE),
    dir=c("==",
          "==",
          "==",
          "=="),
    rhs=c(p[2,2],  # p_alpha|alpha/f
          p[1,2],  # p_beta|alpha/f
          p[2,1],  # p_alpha|beta/m
          p[1,1])  # p_beta|beta/m
  )
}
ublp <- function(alpha,beta) {
  p<-p_D.G(alpha,beta)
  f <- lpf(p)
  result <- lp("max", f$obj, f$con, f$dir, f$rhs)
#  result$solution
  result$objval / p[2,2]
}
lblp <- function(alpha,beta) {
  p<-p_D.G(alpha,beta)
  f <- lpf(p)
  result <- lp("min", f$obj, f$con, f$dir, f$rhs)
  rho <- result$solution
#  cat(2,2,p[2,2],rho[1] + rho[3],'\n')
#  cat(1,2,p[1,2],rho[2] + rho[4],'\n')
#  cat(2,1,p[2,1],rho[1] + rho[2],'\n')
#  cat(1,1,p[1,1],rho[3] + rho[4],'\n')
  result$objval / p[2,2]
}
for (i in 1:6) 
  for (j in 1:6) 
    if (i != j ) {
      N_Y.D <- apply(UCBAdmissions,c(1,3),sum)
      diff_Y.D <- N_Y.D[1,j] / (N_Y.D[1,j] + N_Y.D[2,j]) - N_Y.D[1,i] / (N_Y.D[1,i] + N_Y.D[2,i])
      N_Y.G <- apply(UCBAdmissions[,,c(i,j)],c(1,2),sum)
      diff_Y.G <- N_Y.G[1,2] / (N_Y.G[1,2] + N_Y.G[2,2]) - N_Y.G[1,1] / (N_Y.G[1,1] + N_Y.G[2,1])
      cat(i,j,lb(i,j),'=',lblp(i,j),ub(i,j),'=',ublp(i,j),diff_Y.D,diff_Y.G,if(diff_Y.D>0) diff_Y.D*lb(i,j) else diff_Y.D*ub(i,j),if(diff_Y.D>0) diff_Y.D*ub(i,j) else diff_Y.D*lb(i,j),'\n')
    }

# more general bound, involving more than just 2 departments

N_D.G <- t(apply(UCBAdmissions,c(2,3),sum))
p_D.G <- function(whichD) {
	A <- matrix(0,length(whichD),2)
  for( d in 1:length(whichD) ) {
    for( g in 1:2 ) {
      A[d,g] <- N_D.G[whichD[d],g] / sum(N_D.G[whichD,g])
    }
  }
  rownames(A)<-rownames(N_D.G)[whichD]
  colnames(A)<-colnames(N_D.G)
	A
}
N_Y.D <- t(apply(UCBAdmissions,c(1,3),sum))
p_Y.D <- N_Y.D[,1] / rowSums(N_Y.D)
ub <- function(whichD,d,d2) { # upper bound for rho_{d,d2}
	min(p_D.G(whichD)[d,2],p_D.G(whichD)[d2,1]) / p_D.G(whichD)[d,2]
}
lb <- function(whichD,d,d2) { # lower bound for rho_{d,d2}
  S <- 1
  for( d3 in 1:length(whichD) ) 
    if( d3 != d2 ) {
      S <- S - min(1,p_D.G(whichD)[d3,1] / p_D.G(whichD)[d,2])
    }
  S
}
lpf <- function(p,d,d2) {
  nD <- dim(p)[1]
  f.obj <- rep(0,nD*nD)
  f.obj[d+(d2-1)*nD] <- 1
  f.con <- matrix(0,nD*2,nD*nD)
  for( d3 in 1:nD )
    for( d4 in 1:nD ) 
      f.con[d3,(d4-1)*nD+d3] <- 1
  for( d3 in 1:nD )
    for( d4 in 1:nD ) 
      f.con[d3+nD,d4+(d3-1)*nD] <- 1
  f.dir <- rep("==",nD*2)
#  f.rhs = as.vector(p)  # different convention!
  f.rhs = c(p[,2],p[,1])
  f <- list(obj=f.obj, con=f.con, dir=f.dir, rhs=f.rhs)
}
ublp <- function(whichD,d,d2) {
  p <- p_D.G(whichD)
  f <- lpf(p,d,d2)
  result <- lp("max", f$obj, f$con, f$dir, f$rhs)
  rho <- result$solution
  result$objval / p[d,2]
}
lblp <- function(whichD,d,d2) {
  p <- p_D.G(whichD)
  f <- lpf(p,d,d2)
  result <- lp("min", f$obj, f$con, f$dir, f$rhs)
  rho <- result$solution
  result$objval / p[d,2]
}
#Only 2 departments:
#for (i in 1:6) 
#  for (j in 1:6) 
#    if (i != j ) {
#      whichD <- c(i,j)
#      d <- 1
#All departments:
for (i in 1:6) {
      whichD <- c(1,2,3,4,5,6)
      d <- i
#Departments 3,2 and one more
#for (i in c(1,4,5,6)) {
#      whichD <- c(3,2,i)
#      d <- 1
      lS <- 0
      uS <- 0
      for( d2 in 1:length(whichD) ) 
        if( d2 != d ) {
          if( p_Y.D[whichD[d2]] - p_Y.D[whichD[d]] > 0 ) {
            cat('  ',lblp(whichD,d,d2),lb(whichD,d,d2),ublp(whichD,d,d2),ub(whichD,d,d2),'\n')
            lS <- lS + (p_Y.D[whichD[d2]] - p_Y.D[whichD[d]]) * lblp(whichD,d,d2)
            uS <- uS + (p_Y.D[whichD[d2]] - p_Y.D[whichD[d]]) * ublp(whichD,d,d2)
          } else {
            lS <- lS + (p_Y.D[whichD[d2]] - p_Y.D[whichD[d]]) * ublp(whichD,d,d2)
            uS <- uS + (p_Y.D[whichD[d2]] - p_Y.D[whichD[d]]) * lblp(whichD,d,d2)
          }
        }
      cat(i,j,lS,uS,'\n')
    }

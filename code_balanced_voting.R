#packages: gridExtra, tidyverse, ggpubr, ggplot2,
#forcats, gridExtra,purr,readr,reshape2
#stringr, tibble, tidyr,
library(gridExtra)
library(tidyverse)
library(ggpubr)
library(ggplot2)
library(forcats)
library(gridExtra)
library(purrr)
library(readr)
library(reshape2)
library(stringr)
library(tibble)
library(tidyr)

############################## Functions #####################################


#spin-off function of choose for proof of fact 1 

choose_1 <-function(n){choose(n,n/2)}

#P function, it is designed to satisfy the condition P(n)=P(n-1) for n odd

P<-function(n){
  if(n==1){
    1
  }else if(n%%2==1){
    m<-(n-1)/2
    v<-(m+1:m)/(4*(1:m))
    1/2 + prod(v)/2
  }else{
    m<-(n)/2
    v<-(m+1:m)/(4*(1:m))
    1/2 + prod(v)/2
  }
}

#Prob function of probability that a voting round with m players results in N losers


Prob <-function(m,N){
  if(N==0){
    1/(2^(m-1))
  }else if (m==0){
    1
  } else {
  v_1<-(1:m)/2
  v_2<-c(rep(1,m-N),1:N)
  v_3<-c((m-N):1,rep(1,N))
  p<-prod(v_1/(v_2 * v_3))
  if (N==(m/2)){
    p
  } else {
    2*p
    }
}
}


#Prob function of probability that a voting round with m players results in at least 1 loser

Prob_Y<-function(m){1-1/(2^(m-1))}




#Phi and Lambda functions

Phi<-function(N,n){
  if(n==1){
  1
}else{
  t<-1:floor(n/2)
  v_1<-sapply(N-n+t,P)
  v_2<-sapply(t,Prob,m=n)
  sum(v_1*v_2)/Prob_Y(n)
}
}

Lambda<-function(N,n){
  t<-0:floor(n/2)
  V_1<-sapply(N-n+t,P)
  V_2<-sapply(t,Prob,m=n)
  sum(V_1*V_2)
}

#spin-off function of lambda for proof of fact 1 

Lambda_1<-function(N){Lambda(N,N-1)}



#Theta function


Theta<-function(N){
  t<-1:floor(N/2)
  v_1<-sapply(t,P)
  v_2<-sapply(t,Prob,m=N)
  sum(v_1*v_2)/Prob_Y(N)
}


#M_0,M_1,M_2 functions for proof of proposition 1

M_0 <-function(N){
  (P(N)-1/2)/(1-P(N))
}

M_1 <-function(N,x){
  L<-Lambda(N,x)
  p<-P(x+1)
  phi<-Phi(N,x+1)
  (L-p/2-(1-p)*phi)/(p-1/2)
}

M_2<-function(N){
  (Lambda(N,N-1)-P(N)*(P(N)/(2^(N-1))+(1-1/(2^(N-1)))/2)-(1-P(N))*Theta(N))/(P(N)-1/2)
}

M_1_max<-function(N){
  M_1(N,N-2)
}

M_1_min<-function(N){
  M_1(N,1)
}



#Proof that M_1 is monotonically increasing in x for N in [3,1000] 
#First we define a function that gives true iff M_1 is monotonically increasing in x given N

monotonic<-function(N){
  m<-sapply(1:(N-2), M_1,N=N)
  all(m == cummax(m))
  #!is.unsorted(m)
}

#Secondly we test numerically all N between 3 and 1000
#N_1000<-3:1000
#all(sapply(N_1000, monotonic)) don't run this!!! (Highly Inefficient)



#functions H_crit value and epsilon_crit value for equilibrium under BV

H_crit<-function(N){
  max(c(M_0(N),M_1(N,N-2),M_2(N)))
}

e_crit<-function(N){
  min(c(M_0(N),4*Lambda(N,1)-Phi(N,2)-3/2))
}


#MM_3,M_4 functions for proof of Lemma 1


M_3<-function(N,x){
  (P(N-x)-0.5)/(P(x+1)-0.5)
}

M_4<-function(N){
  p<-P(N)
  (1-p)/(p-0.5)
}

M_3_max<-function(N){
  M_3(N,N-2)
}

M_3_min<-function(N){
  M_3(N,1)
}


#functions H_crit_ST value and epsilon_crit_ST value for 
#equilibrium under ST

H_crit_st <-function(N){
  p<-P(N)
  (1-p)/(p-1/2)
}

e_crit_st <-function(N){
  p<-P(N)
  (p-1/2)/(1-p)
}


#H_SM function for sufficient conditions for which SI agents prefer
#BV to SM if 0<N_s<N


H_SM<-function(N,n){
  PN<-P(N)
  pn<-P(n)
  phi<-Phi(N,n)
  (PN-pn/2-(1-pn)*phi)/(pn-PN)
}





#epsilon function that gives iff condition of epsilon such that WI agents prefer BV to SM

e_SM <-function(N,n){
  l<-Lambda(N,n)
  Pr<-P(N)
  (l-Pr)/(Pr-1/2)
}

#Q function for sufficient conditions for which SI agents prefer BV to SM if N_s=N

Q<-function(N){
  q<-P(N)
  q*(-0.5+(2*q-1)/(2^(N))) + Theta(N)*(1-q)
}

#Functions used in Utility comparison BV vs. SM

#Binomial coefficient probability distribution with parameter p (has to be redesigned due to large N)

Binom <-function(N,n,p){
  if(N==0){
    1
  }else if(n %in% c(0,N)) {
    p^(n) * (1-p)^(N-n)
  }else{
    v_1<-(1:N)*c(rep(p,n),rep(1-p,N-n))
    v_2<-c(1:(N-n),1:n)
    prod(v_1/v_2)
  }
}

#M(N,p) function

M<-function(N,p){
  Ns<-1:(N-1)
  Pr<-P(N)
  pr<-sapply(Ns, P)
  bi<-sapply(Ns, Binom,N=N,p=p)
  nume<-sum(bi*(N-Ns)*(Pr-1/2))
  deno<-sum(bi*Ns*(pr-Pr))
  nume/deno
}

#C function

C<-function(N,p){
  Ns<-1:(N-1)
  Pr<-P(N)
  pr<-sapply(Ns, P)
  bi<-sapply(Ns, Binom,N=N,p=p)
  phi<-sapply(Ns, Phi,N=N)
  lambda<-sapply(Ns, Lambda,N=N)
  theta<-Theta(N)
  nume<-sum(bi*((N-Ns)*(Pr-lambda)+ Ns*(Pr-pr/2-(1-pr)*phi) ))+
        (p^N) * N *(Pr*(1/2 +(1/2)^N  -Pr/(2^(N-1)) )-(1-Pr)*theta)
  deno<-sum(bi*Ns*(pr-Pr))
  nume/deno
}

#C_bar function

C_bar<-function(N,p){
  Ns<-1:(N-1)
  Pr<-P(N)
  pr<-sapply(Ns, P)
  bi<-sapply(Ns, Binom,N=N,p=p)
  phi<-sapply(Ns, Phi,N=N)
  lambda<-sapply(Ns, Lambda,N=N)
  theta<-Theta(N)
  sum(bi*( (N-Ns)*(-lambda)+ Ns*(-pr/2-(1-pr)*phi) ))+
    N*Pr*(1-p^N-(1-p)^N)  +
    (p^N) * N *(Pr*(1/2 +(1/2)^N  -Pr/(2^(N-1)) )-(1-Pr)*theta)
}

#K function

K<-function(N,p){
  Ns<-1:(N-1)
  Pr<-P(N)
  pr<-sapply(Ns, P)
  pr_sN<-sapply(N-Ns, P)
  bi<-sapply(Ns, Binom,N=N,p=p)
  phi<-sapply(Ns, Phi,N=N)
  lambda<-sapply(Ns, Lambda,N=N)
  theta<-Theta(N)
  
  sum(bi*(Ns*((1-pr)*phi +pr/2-1/2) -(N-Ns)*(pr_sN-lambda) ))+
    (p^N)*N*Q(N)
}

#N_st function that gives N large enough
# given p  such that BV gives higher welfare
# than ST


N_st<-function(p){
  N<-4
  while (K(N,p)<=0) {
    N = N+1
  }
  return(N)
} 



#e_MV function that gives sufficent low epsilon such that
# WI agents prefer BV to MV with Ns SI agents

e_MV<-function(N,n){
  Pr<-P(N)
  theta<-Theta(N)
  lambda<-Lambda(N,n)
  (lambda-Pr*(1/2+(Pr-1/2)/(2^(N-1))) -(1-Pr)*theta )/(Pr-1/2)
}

#H_MV function that gives sufficent high H such that
# SI agents prefer BV to MV with Ns SI agents

H_MV<-function(N,n){
  Pr<-P(N)
  pr<-P(n)
  theta<-Theta(N)
  phi<-Phi(N,n)
  ( Pr*(1/2+(Pr-1/2)/(2^(N-1))) + (1-Pr)*theta +
      -(1-pr)*phi -pr/2 )/(pr-Pr)
}
  
H_MV_max<-function(N){
  if(N%%2==0){
  n<-1:(N-1)
  }else {
  n<-1:(N-2)
  }
  max(sapply(n, H_MV,N=N))
}


#D function


D<-function(N,p){
  Ns<-1:(N-1)
  Pr<-P(N)
  pr<-sapply(Ns, P)
  bi<-sapply(Ns, Binom,N=N,p=p)
  phi<-sapply(Ns, Phi,N=N)
  lambda<-sapply(Ns, Lambda,N=N)
  theta<-Theta(N)
  q<-Q(N)
  nume<-sum(bi*((N-Ns)*(-lambda)+ Ns*(-pr/2-(1-pr)*phi) ))+
    (Pr+q)*(1-p^N-(1-p)^N)*N   +
    ((1-p)^N) * N *q
  deno<-sum(bi*Ns*(pr-Pr))
  nume/deno
}




################# Plots ###############################



#Figure 1: THe Prob of Winning P(n) vs. the Number of Voting Agents n

N<-20
p<-sapply(1:N,P)
df1<-data.frame(n=1:N,P=p)
plot1 <-df1 %>%
  ggplot(aes(n,P)) + geom_line()

plot1

# Figure 2: Theta(n), Lambda(N,n), Phi(N,n), P(N)

N<-20

phi<-sapply(2:(N-1),Phi,N=N)
p<-rep(P(N),18)
lambda<-sapply(2:(N-1),Lambda,N=N)
theta<-rep(Theta(N),18)

df2<-data.frame(n=2:(N-1),Phi=phi,P=p,Lambda=lambda,Theta=theta)

plot2<-df2 %>% melt(id.vars="n",variable.name = "Functions")%>%
  ggplot(aes(n,value)) + geom_line(aes(colour = Functions))

plot2



#Figure 3: epsilon_crit(N) vs the number of agents N.

N<-200
E_crit<-sapply(3:N,e_crit)
df3<-data.frame(N=3:N,e_crit=E_crit)
plot3 <-ggline(df3,"N","e_crit")

plot3


#Figure 4: H_crit_st and e_crit_st  vs. N

N<-200

H_st<-sapply(3:N,H_crit_st)
e_st<-sapply(3:N,e_crit_st)

df4.1<-data.frame(N=3:N,H_crit_st=H_st)
df4.2<-data.frame(N=3:N,e_crit_st=e_st)
plot4.1<-df4.1 %>% ggplot(aes(N,H_crit_st)) + geom_line()
plot4.2<-df4.2 %>% ggplot(aes(N,e_crit_st)) + geom_line()


plot4<-grid.arrange(plot4.1, plot4.2, ncol=2)






#Figure B.1 graph of M_1
#N=200 and 0<x<N-1

N<-200

m_1<-sapply(1:(N-2),M_1,N=N)
dfB1<-data.frame(x=1:(N-2),M_1=m_1)

plotB1<-dfB1 %>% ggplot(aes(x,M_1)) + geom_line()
plotB1



#Figure B.2 plot of M_0, M_1_max, M_1_min, M_2

N<-200
M_1_m_N<-sapply(3:N,M_1_min)
M_1_M_N<-sapply(3:N,M_1_max)
M_0_N<-sapply(3:N, M_0)
M_2_N<-sapply(3:N, M_2)

dfB2.1<-data.frame(N=3:N ,M_1_min=M_1_m_N , M_1_max=M_1_M_N , M_2=M_2_N , M_0 =M_0_N)
dfB2.2<-dfB2.1 %>% filter(N %in% 3:20)
dfB2.1<-melt(dfB2.1,id.vars="N",variable.name = "functions")
dfB2.2<-melt(dfB2.2,id.vars="N",variable.name = "functions")

plotB2.1<-ggplot(dfB2.1, aes(N,value)) + geom_line(aes(colour = functions))
plotB2.2<-ggplot(dfB2.2, aes(N,value)) + geom_line(aes(colour = functions))
plotB2<-grid.arrange(plotB2.1, plotB2.2, ncol=2)

plotB2


#Figure B.3 plots of  H_crit and epsilon_crit
N<-200
H_Crit<-sapply(3:N,H_crit)
e_Crit<-sapply(3:N,e_crit)
dfB3.1<-data.frame(N=3:N ,H_crit=H_Crit)
dfB3.2<-data.frame(N=3:N ,e_crit=e_Crit)
plotB3.1<-ggplot(dfB3.1, aes(N,H_crit)) + geom_line()
plotB3.2<-ggplot(dfB3.2, aes(N,e_crit)) + geom_line()
plotB3<-grid.arrange(plotB3.1, plotB3.2, ncol=2)

plotB3



#Figure B.4 plot of M_0, M_3_max, M_3_min, M_4

N<-200
M_3_m_N<-sapply(3:N,M_3_min)
M_3_M_N<-sapply(3:N,M_3_max)
M_0_N<-sapply(3:N, M_0)
M_4_N<-sapply(3:N, M_4)

dfB4<-data.frame(N=3:N ,M_3_min=M_3_m_N , M_3_max=M_3_M_N , M_4=M_4_N , M_0 =M_0_N)%>%
      melt(id.vars="N",variable.name = "functions")


plotB4<-ggplot(dfB4, aes(N,value)) + geom_line(aes(colour = functions))


plotB4





#Figure C.1 graph of e_SM
#N=20,200 and 0<Ns<N-1
N1<-200
N2<-20
e_sm1<-sapply(1:(N1-1),e_SM,N=N1)
e_sm2<-c(sapply(1:(N2-1),e_SM,N=N2),rep(NaN,N1-N2))
e_Crit1<-rep(e_crit(N1),N1-1)
e_Crit2<-c(rep(e_crit(N2),N2-1),rep(NaN,N1-N2))

dfC1<-data.frame(Ns=1:(N1-1) ,e_sm1=e_sm1 , e_sm2=e_sm2 , e_Crit1=e_Crit1 , e_Crit2=e_Crit2)%>% 
       melt(id.vars="Ns",variable.name = "functions")

plotC1<-ggplot(dfC1, aes(Ns,value)) + geom_line(aes(colour = functions))

plotC1


#Figure C.2 graph of Q(N) vs the number of agents N
#3<=N<=200
N<-200
q<-sapply(3:N,Q)
dfC2<-data.frame(N=3:N,Q=q)
plotC2<-ggplot(dfC2, aes(N,Q)) + geom_line()


plotC2



#Figure C.3 graph of H_SM
#N=20,200 and 0<N_s<N-1
N1<-20
N2<-200
H_sm1<-sapply(1:(N1-1),H_SM,N=N1)
H_sm2<-sapply(1:(N2-1),H_SM,N=N2)
dfC3.1<-data.frame(Ns=1:(N1-1),H_SM=H_sm1)
dfC3.2<-data.frame(Ns=1:(N2-1),H_SM=H_sm2)
plotC3.1<-ggplot(dfC3.1, aes(Ns,H_SM)) + geom_line()
plotC3.2<-ggplot(dfC3.2, aes(Ns,H_SM)) + geom_line()

plotC3<-grid.arrange(plotC3.1, plotC3.2, ncol=2)

plotC3

#Figure C.4: H vs. W_BV=W_SM to hold when N=20

H0.1<-C(20,0.1)+M(20,0.1)*(1:999 /1000)
H0.33<-C(20,1/3)+M(20,1/3)*(1:999 /1000)
H0.66<-C(20,2/3)+M(20,2/3)*(1:999/1000)
H0.9<-C(20,0.9)+M(20,0.9)*(1:999 /1000)
e<-1:999 /1000

dfC4<-data.frame(e=e ,H0.1=H0.1 , H0.33=H0.33 , H0.66=H0.66 , H0.9=H0.9)%>%
  melt(id.vars="e",variable.name = "plots")

plotC4<-ggplot(dfC4, aes(e,value)) + 
        geom_line(aes(colour = plots))+
        geom_vline(xintercept = e_crit(20), 
        linetype="dashed",color = "black", size=1)+
        geom_hline(yintercept = 1)

plotC4




#Figure C.5: K(N,p) Vs.p

p<-1:999 /1000
K3<-sapply(p,K,N=3)
K4<-sapply(p,K,N=4)
K8<-sapply(p,K,N=8)
K16<-sapply(p,K,N=16)
K23<-sapply(p,K,N=23)
K52<-sapply(p,K,N=52)

dfC5.1<-data.frame(p=p ,K3=K3 , K4=K4 , K8=K8 , K16=K16,K52=K52)%>%
  melt(id.vars="p",variable.name = "plots")
dfC5.2<- dfC5.1 %>%filter(p >=0.5)

plotC5.1<-ggplot(dfC5.1, aes(p,value)) +
          geom_hline(yintercept = 0)+ 
          geom_line(aes(colour = plots))
plotC5.2<-ggplot(dfC5.2, aes(p,value)) +
          geom_hline(yintercept = 0)+ 
          geom_line(aes(colour = plots))

plotC5<-plotB3<-grid.arrange(plotC5.1, plotC5.2, ncol=2)

plotC5


#Figure C.6: N_st(p) Vs.p

p<-60:99 /100
nst<-sapply(p,N_st)
dfC6<-data.frame(p,N_st=nst)

plotC6<-ggplot(dfC6, aes(p,N_st)) +
  geom_line()

plotC6


#Figure C.7: e_MV(N,1)-e_crit(N) Vs.N

N<-3:200
eme<-sapply(N,e_MV,n=1)-sapply(N,e_crit)
dfC7<-data.frame(N,min_e_SV_minus_e_crit=eme)

plotC7<-ggplot(dfC7, aes(N,min_e_SV_minus_e_crit)) +
  geom_line()+geom_hline(yintercept = 0)
  

plotC7


#Figure C8

N<-3:200
H_mv<-sapply(N,H_MV_max)
dfC8<-data.frame(N=N,H_SV_max=H_mv)

plotC8<-ggplot(dfC8, aes(N,H_SV_max)) +
  geom_line()


plotC8


#Figure C.9: H vs. W_BV=W_MV to hold when N=20

H0.1<-D(20,0.1)+M(20,0.1)*(1:999 /1000)
H0.33<-D(20,1/3)+M(20,1/3)*(1:999 /1000)
H0.66<-D(20,2/3)+M(20,2/3)*(1:999/1000)
H0.99<-D(20,0.99)+M(20,0.9)*(1:999 /1000)
e<-1:999 /1000

dfC9<-data.frame(e=e ,H0.1=H0.1 , H0.33=H0.33 , H0.66=H0.66 , H0.99=H0.99)%>%
  melt(id.vars="e",variable.name = "plots")

plotC9<-ggplot(dfC9, aes(e,value)) + 
  geom_line(aes(colour = plots))+
  geom_vline(xintercept = e_crit(20), 
             linetype="dashed",color = "black", size=1)+
  geom_hline(yintercept = 1)

plotC9




#plot of theta for N in [3,200]

#Figure graph of Theta
#N=200 and 0<x<N-1
N<-200
theta<-sapply(3:N,Theta)
df<-data.frame(x=1:(N-2),theta=theta)
ggline(df,"x","theta")






######################## Numerical Facts ########################




#Function that computes all values of Prob given m (length floor(M/2)+1)

P_n<-function(m){
  N<-floor(m/2)
  if(N==0){
    return(1)
  }
  Pm<-0:N
  Pm[N+1]<-Prob(m,N)
  for(i in N:1){
    Pm[i]<-Pm[i+1]*(i)/(m-i+1)
  }
  if(m%%2==1){
    Pm
  }else{
    Pm[-(N+1)]<-Pm[-(N+1)]*2
    Pm
  }
}






# Function that tests if M_1 is monotonic for all N in [3,M]

M_1_monotone<-function(M){
  N<-3
  logical<-vector()
  Pr<-sapply(1:M, P)
  PY<-sapply(1:M, Prob_Y)
  
  while(N<=M){
    l<-vector()
    n<-1
    lambda<-Lambda(N,1)
    
    while(n+1<N){
      Pn<-P_n(n+1)
      v<-Pr[(N-n-1)+(0:floor((n+1)/2))]*Pn
      
      phi<-sum(v[-1])/PY[n+1]
      
      m<-(lambda-Pr[n+1]/2 -(1-Pr[n+1])*phi)/(Pr[n+1]-0.5)
      
      l<-c(l,m)
      lambda<-phi*PY[n+1]+v[1]
      #lambda<-sum(v)
      n<-n+1
    }
    
    if(!(all(l == cummax(l)))){
      return(c(N))
    }
    
    N<-N+1
  }
  return(TRUE)
}

#function that tests if C is positive for all N in [3,M]

C_positive<-function(M){
  logical<-vector()
  ps<-1:500 / 1000
  Pr<-sapply(1:M, P)
  PY<-sapply(1:M, Prob_Y)
  theta<-1:M
  for(N in 3:M){
    n<-floor(N/2)   
    v1<-Pr[1:n]  
    v2<-P_n(N)[-1]
    theta[N]<-sum(v1*v2)/PY[N]
  }
  
  q<- Pr*(1/2+(1/2)^(1:M) -Pr/(2^(1:M-1)) ) - theta*(1-Pr)
  
  for(N in 3:M){    
    l<-vector()
    
    lambda<-unlist(MLP10000[[N]])
    phi<-unlist(MLP10000[[10000+N]])
    for(p in ps){  
      binomp<-dbinom(1:(N-1),N,p)
      
      Ns<-1:(N-1)
      vp<-sum( binomp*((N-Ns)*(Pr[N]-lambda[Ns])+
                         Ns*(Pr[N]-Pr[Ns]/2-(1-Pr[Ns])*phi[Ns]) )  )
      
      vmp<-sum(binomp[(N-1):1]*((N-Ns)*(Pr[N]-lambda[Ns])+
                                  Ns*(Pr[N]-Pr[Ns]/2-(1-Pr[Ns])*phi[Ns]))) 
      
      
      vp<- (vp)+N*q[N]*(p^N)
      vmp<- (vmp)+N*q[N]*((1-p)^N)
      
      
      
      
      
      if(!(all(c(vp,vmp)>0))){
        return(c(vp,vmp,p,N))
      }
    }
    
  } 
  TRUE
}

#function that tests if Q is negative for all N in [3,M]

Q_Negative<-function(M){
  logical<-vector()
  Pr<-sapply(1:M, P)
  PY<-sapply(1:M, Prob_Y)
  theta<-1:M
  for(N in 3:M){
    n<-floor(N/2)   
    v1<-Pr[1:n]  
    v2<-P_n(N)[-1]
    theta[N]<-sum(v1*v2)/PY[N]
  }
  
  all( (Pr*(1/2+(1/2)^(1:M) -Pr/(2^(1:M-1)) ) - theta*(1-Pr))[3:M]>0)
}

#function that tests if for all N K(N,p) has a zero for some p in ]0,1[


K_zero<-function(M){
  Pr<-sapply(1:M, P)
  PY<-sapply(1:M, Prob_Y)
  theta<-1:M
  for(N in 3:M){
    n<-floor(N/2)   
    v1<-Pr[1:n]  
    v2<-P_n(N)[-1]
    theta[N]<-sum(v1*v2)/PY[N]
  }
  
  q<- Pr*(1/2+(1/2)^(1:M) -Pr/(2^(1:M-1)) ) - theta*(1-Pr)
  
  for(N in 4:M){    
    
    
    lambda<-unlist(MLP10000[[N]])
    phi<-unlist(MLP10000[[10000+N]])
    for(p in 0.5){  
      binomp<-Binomp(N,p)
      
      Ns<-1:(N-1)
      vp<-sum( binomp*((Ns-N)*(Pr[N-Ns]-lambda[Ns])+
                         Ns*(Pr[Ns]/2+(1-Pr[Ns])*phi[Ns]-0.5) )  )
      
      
      vp<- (vp)-N*q[N]*(p^N)
      
      
      
      
      if(!(vp>0)){
        return(c(vp,p,N))
      }
    }
    
  } 
  return(TRUE)
}





# Function that checks if H_crit(N) is less than 1 for all N in [3,M]\{6}

H_crit_less<-function(M){
  l<-vector()
  Pr<-sapply(1:M, P)
  PY<-sapply(1:M, Prob_Y)
  theta<-1:M
  for(N in 3:M){
    n<-floor(N/2)   
    v1<-Pr[1:n]  
    v2<-P_n(N)[-1]
    theta[N]<-sum(v1*v2)/PY[N]
  }
  for(N in 3:M){    
    
    
    lambda<-unlist(MLP10000[[N]])
    phi<-unlist(MLP10000[[10000+N]])
    
    m0<-(Pr[N]-0.5)/(1-Pr[N])
    
    m1<-(lambda[N-2]-Pr[N-1]/2 -(1-Pr[N-1])*phi[N-1])/(Pr[N-1]-0.5)
    
    m2<-(lambda[N-1]-Pr[N]*(Pr[N]/(2^(N-1))+0.5*(1-1/(2^(N-1))) )+
           -(1-Pr[N])*theta[N])/(Pr[N]-0.5)
    if(!N==6){
      l<-c(l,max(c(m0,m1,m2))<=1)
    }
  }
  all(l)
}






#Function that tests if D+M*_crit <=1





BV_MV<-function(M){
  ps<-1:500 / 1000
  Pr<-sapply(1:M, P)
  PY<-sapply(1:M, Prob_Y)
  theta<-1:M
  for(N in 3:M){
    n<-floor(N/2)   
    v1<-Pr[1:n]  
    v2<-P_n(N)[-1]
    theta[N]<-sum(v1*v2)/PY[N]
  }
  
  q<- Pr*(1/2+(1/2)^(1:M) -Pr/(2^(1:M-1)) ) - theta*(1-Pr)
  
  for(N in 8:M){    
    
    
    lambda<-unlist(MLP10000[[N]])
    phi<-unlist(MLP10000[[10000+N]])
    
    for(p in ps){  
      binomp<-dbinom(1:(N-1),N,p)
      Ns<-1:(N-1)
      
      Dbar1<-sum( binomp*((N-Ns)*(Pr[N]-q[N]-lambda[Ns])+
                            Ns*(Pr[N]-q[N]-Pr[Ns]/2-(1-Pr[Ns])*phi[Ns]) )  )
      Dbar1<- Dbar1-N*q[N]*((1-p)^N)
      
      Dbar2<-sum(binomp[(N-1):1]*((N-Ns)*(Pr[N]-q[N]-lambda[Ns])+
                                    Ns*(Pr[N]-q[N]-Pr[Ns]/2-(1-Pr[Ns])*phi[Ns]) )  ) 
      Dbar2<- Dbar2-N*q[N]*((p)^N)
      
      Dbar<-c(Dbar1,Dbar2)
      
      Mbar1<-sum( binomp*(N-Ns)*(Pr[N]-0.5))
      Mbar2<-sum( binomp[(N-1):1]*(N-Ns)*(Pr[N]-0.5))
      
      Mbar<-c(Mbar1,Mbar2)
      
      ecrit<-min(c((Pr[N]-0.5)/(1-Pr[N]), 4*lambda[1]-phi[2]-1.5))
      
      deno1<-sum( binomp*Ns*(Pr[Ns]-Pr[N]))
      deno2<-sum( binomp[(N-1):1]*Ns*(Pr[Ns]-Pr[N]))
      
      deno<-c(deno1,deno2)
      
      
      
      
      if(!all(Dbar+Mbar*ecrit<=deno )){
        return(c(Dbar1,Mbar1,ecrit,p,N))
      }
    }
    
  } 
  return(TRUE)
}



#Function that tests if K(N,p)>0 for all N in [4,10000], p<=0.6 steps 0,01


K_positive_0.6<-function(M){
  ps<-1:600/1000
  Pr<-sapply(1:M, P)
  PY<-sapply(1:M, Prob_Y)
  theta<-1:M
  for(N in 3:M){
    n<-floor(N/2)   
    v1<-Pr[1:n]  
    v2<-P_n(N)[-1]
    theta[N]<-sum(v1*v2)/PY[N]
  }
  
  q<- Pr*(1/2+(1/2)^(1:M) -Pr/(2^(1:M-1)) ) - theta*(1-Pr)
  
  for(N in 4:M){    
    
    
    lambda<-unlist(MLP10000[[N]])
    phi<-unlist(MLP10000[[10000+N]])
    for(p in ps){  
      binomp<-dbinom(1:(N-1),N,p)
      
      Ns<-1:(N-1)
      vp<-sum( binomp*((Ns-N)*(Pr[N-Ns]-lambda[Ns])+
                         Ns*(Pr[Ns]/2+(1-Pr[Ns])*phi[Ns]-0.5) )  )
      
      
      vp<- (vp)-N*q[N]*(p^N)
      
      
      
      
      
      if(!(vp>=0)){
        return(c(vp,p,N))
      }
    }
    
  } 
  return(TRUE)
}


#function that gives list with all values of Lambda and Phi 

MLP<-function(M){
  mat<-list()
  mat[[1]]<-1
  mat[[1+M]]<-1
  mat[[2]]<-1
  mat[[2+M]]<-1
  Pr<-sapply(1:M,P)
  PY<-sapply(1:M,Prob_Y)
  for(N in 3:M){
    lambda<-1:(N-1)
    phi<-1:(N-1)
    for(Ns in 1:(N-1)){
      n<-floor(Ns/2)
      Pn<-P_n(Ns)
      lambda[Ns]<-sum(Pr[(N-Ns)+0:n]*Pn)
      phi[Ns]<-(lambda[Ns]-Pr[N-Ns]*Pn[1])/PY[Ns]
    }
    phi[1]<-1
    
    mat[[N]]<-lambda
    mat[[M+N]]<-phi
  }
  return(mat)
}

#function that test if for given p in ]0.6,1[ there exist a unique N_p large enough
# such that K(N,p)>0 iff N>=N_p


K_positive_1<-function(M){
  ps<-601:999/1000
  Pr<-sapply(1:M, P)
  PY<-sapply(1:M, Prob_Y)
  theta<-1:M
  for(N in 3:M){
    n<-floor(N/2)   
    v1<-Pr[1:n]  
    v2<-P_n(N)[-1]
    theta[N]<-sum(v1*v2)/PY[N]
  }
  
  q<- Pr*(-1/2-(1/2)^(1:M) +Pr/(2^(1:M-1)) ) + theta*(1-Pr)
  
  for(p in ps){  
    vp<- -1
    for(N in 4:M){    
      lambda<-unlist(MLP10000[[N]])
      phi<-unlist(MLP10000[[10000+N]])
      t<-vp  
      
      binomp<-dbinom(1:(N-1),N,p)
      
      
      
      Ns<-1:(N-1)
      vp<-sum( binomp*(Ns*(Pr[Ns]/2+(1-Pr[Ns])*phi[Ns]-0.5) -(N-Ns)*(Pr[N-Ns]-lambda[Ns])) )  
      
      vp<- (vp)+N*q[N]*(p^N)
      
      
      if((vp<0)&(t>=0)){
        return(c(t,vp,p,N))
      }
      if((vp<0)&(N==10000)){
        return(c(vp,p,N))
      }
      
    }
  } 
  return(TRUE)
}


#function that test if e_{MV}(N,1)-E_crit>0 for all N in [8,10000]


EMV_Ecrit<-function(M){
  Pr<-sapply(1:M, P)
  PY<-sapply(1:M, Prob_Y)
  theta<-1:M
  for(N in 3:M){
    n<-floor(N/2)   
    v1<-Pr[1:n]  
    v2<-P_n(N)[-1]
    theta[N]<-sum(v1*v2)/PY[N]
  }
  
  for(N in 8:M){  
    lambda<-unlist(MLP10000[[N]])[1]
    phi<-unlist(MLP10000[[10000+N]])[2]
    
    e_mv<-(lambda-Pr[N]*(0.5-1/(2^N) + Pr[N]/(2^(N-1)) )-(1-Pr[N])*theta[N])/(Pr[N]-0.5)  
    
    e_cr<-min(c( (Pr[N]-0.5)/(1-Pr[N]) , 4*lambda-phi-1.5))
    if(e_mv<e_cr){
      return(c(N,e_mv,e_cr))
    }
  }
  TRUE
}



#Function that test if H_MV(N,Ms)<=1.26 for all N in [8,10000]


H_MV126<-function(M){
  Pr<-sapply(1:M, P)
  PY<-sapply(1:M, Prob_Y)
  theta<-1:M
  for(N in 3:M){
    n<-floor(N/2)   
    v1<-Pr[1:n]  
    v2<-P_n(N)[-1]
    theta[N]<-sum(v1*v2)/PY[N]
  }
  
  for(N in 3:M){  
    phi<-unlist(MLP10000[[10000+N]])
    
    if(N%%2==1){
      Ns<-1:(N-2)
      
      h_mv<-max(( Pr[N]*(0.5-1/(2^N) + Pr[N]/(2^(N-1)) )-(1-Pr[N])*theta[N] +
                    -(1-Pr[Ns])*phi[Ns] )/(Pr[Ns]-Pr[N])   )
      
    }else {
      Ns<-1:(N-1)
      
      h_mv<-max(( Pr[N]*(0.5-1/(2^N) + Pr[N]/(2^(N-1)) )-(1-Pr[N])*theta[N] +
                    -(1-Pr[Ns])*phi[Ns] )/(Pr[Ns]-Pr[N])   )
    }
    
    if(h_mv>1.26){
      return(c(N,h_mv))
    }
    
  }
  
  TRUE
}




#Function that test if K(N,p) has a unique zero for all N in [4,10000] and p in ]0,1[


K_zero_unique<-function(M){
  ps<-(1:999)/1000
  Pr<-sapply(1:M, P)
  PY<-sapply(1:M, Prob_Y)
  theta<-1:M
  for(N in 3:M){
    n<-floor(N/2)   
    v1<-Pr[1:n]  
    v2<-P_n(N)[-1]
    theta[N]<-sum(v1*v2)/PY[N]
  }
  
  q<- Pr*(1/2+(1/2)^(1:M) -Pr/(2^(1:M-1)) ) - theta*(1-Pr)
  
  for(N in 4:M){    
    l<-vector()
    
    lambda<-unlist(MLP10000[[N]])
    phi<-unlist(MLP10000[[10000+N]])
    for(p in ps){  
      binomp<-dbinom(1:(N-1),N,p)
      
      Ns<-1:(N-1)
      vp<-sum( binomp*((Ns-N)*(Pr[N-Ns]-lambda[Ns])+
                         Ns*(Pr[Ns]/2+(1-Pr[Ns])*phi[Ns]-0.5) )  )
      
      
      vp<- (vp)-N*q[N]*(p^N)
      
      l<-c(l,vp)
    }
    
    for(i in 1:(length(ps)-1)){
      if((l[i]<=0) & (l[i+1]>=0)){
        return(c(ps[i],N,l[i],l[i+1]))
      }
    }
    
  } 
  TRUE
}


#Function that for each p in ]0.6,1[ give the largest N such that K(N,p)<0 
#for N<=10000


negative_K_N<-function(M){
  l<-vector()
  ps<-601:999/100
  Pr<-sapply(1:M, P)
  PY<-sapply(1:M, Prob_Y)
  theta<-1:M
  for(N in 3:M){
    n<-floor(N/2)   
    v1<-Pr[1:n]  
    v2<-P_n(N)[-1]
    theta[N]<-sum(v1*v2)/PY[N]
  }
  
  q<- Pr*(-1/2-(1/2)^(1:M) +Pr/(2^(1:M-1)) ) + theta*(1-Pr)
  
  for(p in ps){  
    n<-4
    for(N in 4:M){    
      lambda<-unlist(MLP10000[[N]])
      phi<-unlist(MLP10000[[10000+N]])
      binomp<-dbinom(1:(N-1),N,p)
      
      Ns<-1:(N-1)
      vp<-sum( binomp*(Ns*(Pr[Ns]/2+(1-Pr[Ns])*phi[Ns]-0.5) -(N-Ns)*(Pr[N-Ns]-lambda[Ns])) )  
      
      vp<- (vp)+N*q[N]*(p^N)
      
      
      if(vp<0){
        n<-N
      }
      
      
    }
    l<-c(l,n)
  } 
  l
}
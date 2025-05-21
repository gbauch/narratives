reset()

##sage-file for the equilibrium calculation within the experiment

#state space = number of red balls in unknown urn
Omega = [1,..,9]

#distribution (uniform)
P = [1/len(Omega) for x in Omega]

#number of balls drawn
K = 3

#set of histories (simplified for sufficient statistic), indicating the number of red balls observed
H = [0,..,K]

#set of models (given h in H)
def M(h):
   if not (h in H):
      raise Exception('not a valid history given')
   Mlis = []
   for ipos in range(h+1):
      for ineg in range(K-h+1):
         Mlis.append((ipos,ineg))
   return(Mlis)


###utility
##

#payoff vector, filled up with zeros afterwards
payoffs = [1300,1000,700,400,100]
while len(payoffs)<len(Omega)+10:
   payoffs.append(0)


#payoffmaximizer out of [1..9] given (thought) relevant numbers of observed red and black balls
def payoffmaximizer (relevanttuple):
   relred,relblack = relevanttuple	
   denom = sum([ P[ix] * (Omega[ix])^relred * (10-Omega[ix])^relblack for ix in range(len(Omega))])
   Pnew = [P[ix] * (Omega[ix])^relred * ((10-Omega[ix]))^relblack / denom for ix in range(len(Omega))]
   
   #payoffcheckloop
   baseutil = 0
   baseguess = Omega[0]
   for x in Omega:		#the 'test candidate' given the choice set to choose from
      
      util = 0
      for iy in range(len(Omega)):	#looping through all true possibilities
         y=Omega[iy]
         util += Pnew[iy] * payoffs[abs(x-y)]
      
      if util == baseutil:
         print('')#print('same utilitylevel occured')
      
      if util > baseutil:
         baseutil = util
         baseguess = x
   return(baseguess)

def expectedpayoff (m,a,b):
   relred,relblack = m
   
   denom = sum([ P[ix] * (Omega[ix])^relred * (10-Omega[ix])^relblack for ix in range(len(Omega))])
   Pnew = [P[ix] * (Omega[ix])^relred * ((10-Omega[ix]))^relblack / denom for ix in range(len(Omega))]
   
   util = sum([Pnew[i] * payoffs[abs(Omega[i]+b-a)] for i in range(len(Omega))])
   
   return(util)
   

def expectednumber (m):
   relred,relblack = m
   X = Omega #from older version, as backup
   #we need to calculate the updated probability
   
   #denominator for the updates: overall probability of making the above (relevant) observation - note that we neglect the binomial coefficient, as it factors out anyway and I don't know on the fly which one it is
   #of course, one could also leave out the divisions by 10...
   denom = sum([ P[ix] * (Omega[ix]/10)^relred * ((10-Omega[ix])/10)^relblack for ix in range(len(Omega))])
   
   Pnew = []
   for ix in range(len(Omega)):
      x = Omega[ix]
      #prob of seeing the numbers if x is describes the true decompositions
      ret = P[ix] * (x/10)^relred * ((10-x)/10)^relblack / denom
      Pnew.append(ret)
   
   #check
   if sum(Pnew) != 1:
      raise Exception('Houston!')
   #print([numerical_approx(el) for el in Pnew])
   
   #the expected number is closest element of X to the updated expectation
   realnumber = sum([Pnew[ix]*Omega[ix] for ix in range(len(Omega))])
   #print('real number would be '+str(numerical_approx(realnumber,digits=4))+' - the rounded number is thus:')
   #return(closestint(realnumber))
   return(realnumber) #that's the belief


def likelihood(m,h): #is this correct?
   s = m[0]+m[1]
   if K < s:
      raise Exception('narrative is longer than history')
   k = m[0]
   
   like = (1/2)^(K-s) * sum([ (Omega[i]/10)^k * ((10-Omega[i])/10)^(s-k) * P[i] for i in range(len(Omega))])
   
   return(like)

##choice function for MLEU equilibria
#If the likelihood of different models are the same, we impose a choice function to consistently pick models (thus, you can strictly rank models by their likelihood, breaking ties)
#The following functions take a model space and derives all consistent choice functions; giving them back to the equilibrium search algorithm
def choicegen(mllow): #generates all consistent choice functions based on ordered lists of models
   #finish pasting
   if len(mllow)==0:
      raise Exception('chocegen was given an empty list of models')
   if len(mllow)==1:
      yield mllow 
      return
   
   #add next step
   val = mllow[0][1]
   mlis = [m for m in filter(lambda x: x[1]==val,mllow)]
   #mrest = mllow[len(mlis):]
   
   for m in mlis:
      for mllownew in choicegen(list(filter(lambda x: x[0]!=m[0],mllow))):
         yield [m]+mllownew

def listchoicefunctions (M,h):
   #checkMh(M,h)
   #need to sort this here!
   ml = sorted([(m, likelihood(m,h)) for m in M],key = lambda tup: -tup[1]) #sort models by decreasing likelihood
   return(choicegen(ml))

def choicefunction (mlis, cml):		#selects the model m from cmlis according to the model-likelihood list / choice function ml
   for x in cml:
      if x[0] in mlis:
         return(x[0])
##

###auxiliary set functions
##


#takes the ordered set A = {a_1, a_2, ...} = {1,2,...} and gives back all monotone partitions, e.g. {0,1}, {2}, {3,4,...N-1}; by the monotonicity property of the reduction lemma, we use these as indexes (range(...)) for the sorted reduced list M of models
def monotonepartition (A):
   if len(A) ==0:
      raise Exception('Empty set given')
   if len(A) == 1:
       yield [ A ]
       return
   
   first = A[0]
   for smaller in monotonepartition(A[1:]):
      yield [ [first] + smaller[0]] + smaller[1:]
      yield [ [first] ] + smaller 


def orderM(Mlis):
   return(sorted(Mlis,key = lambda m: payoffmaximizer(m)))
##


###
#ambiguity rules - deriving optimal actions from subsets
##
def aMEU (mlis,h):
   atest = Omega[0]
   valtest = min_symbolic([expectedpayoff(m,atest,0) for m in mlis])
   for a in Omega[1:]:
      valcomp = min_symbolic([expectedpayoff(m,a,0) for m in mlis])
      if valcomp > valtest:
         atest = a
         valtest = valcomp
   return(atest)
      

def aMLEU (mlis,h,cml):#note, have cml choice list here!
   if len(mlis) == 0:
      raise Exception('Empty narrative list given!')   
   
   likelisall = [(m, likelihood(m,h)) for m in mlis]
   valis = [tup[1] for tup in likelisall]
   #print(likelisall)
   val = valis[0]
   for v in valis:
      if v > val:
         val = v
   
   likelis = [el[0] for el in likelisall if el[1] == val]#list(filter(lambda x: x[1]==val,likelisall))
   
   #print('likelis is '+str(likelis))
   #print('cml is '+str(cml))
   #print('cfunction is '+str(choicefunction(likelis, cml)))
   ##tie-breaking rule (need to include b for sender preferred) - for now just take first element
   ret = payoffmaximizer(choicefunction(likelis, cml))

   return(ret)
##


###eqcheck
##
def eqcheck (sigma,rho,b):
   for mlisi in range(len(sigma)):
      for m in sigma[mlisi]:
         maxEU = max_symbolic([expectedpayoff(m,rhoel,b) for rhoel in rho])
         if expectedpayoff(m,rho[mlisi],b) < maxEU:
            return(False)
   return(True)
#print('cannot have this -> must consider expected payoff')
##


###
#equilibrium finder
##

def findeq(Mlis,h,b,type):
   if type not in ['MLEU','MEU']:
      raise Exception('Equilibrium type' + str(type) + ' not defined.')
   
   if type == 'MEU':
     ambrule = aMEU
   if type == 'MLEU':
      ambrule = aMEU
   
   eqlis = []
   for sigma in monotonepartition(orderM(Mlis)):
      
      if type=='MEU':
         rho = [ambrule(mpart,h) for mpart in sigma]
         if eqcheck(sigma,rho,b):
            eqlis.append((sigma,rho))
      
      
      if type=='MLEU':
         #define choice function
         lchoice = list(listchoicefunctions (Mlis,h))
         for cml in lchoice:
            rho = [aMLEU(mlis, h, cml) for mlis in sigma]
            if eqcheck(sigma,rho,b):
               eqlis.append((sigma,rho,'choice list: '+str(cml)))
   
   return(eqlis)
###



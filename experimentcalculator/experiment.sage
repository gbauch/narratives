reset()

##sage-file for the equilibrium calculation within the experiment

#state space = number of red balls in unknown urn
Omega = [1,..,9]

#distribution (uniform)
P = [1/len(Omega) for x in Omega]

#number of balls drawn
K = 3

#set of histories (full description; 1 for red, 0 for black)
H = [[a,b,c] for a in [0,1] for b in [0,1] for c in [0,1]]

#set of models (given h in H): set of indices for the relevant balls
def M(h):
   if not (h in H):
      raise Exception('not a valid history given')
   Mlis = []
   hpos = sum(h)
   
   for ipos in range(hpos+1):
      for ineg in range(K-hpos+1):
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


def likelihood(m,h):
   if m not in M(h):
      raise Exception('m='+str(m)+' given does not seem to be compatible with the observed data h='+str(h))
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


#determines the corresponding reduced equilibrium
def reduceeq(eq):
   sigma=eq[0]
   rho = eq[1]
   retsigma = []
   retrho = []
   iSet = list(range(len(rho)))
   while len(iSet)!=0:
      i = iSet[0]
      if rho[i] in rho[i:]:
         r = rho[i]
         indexset = [j for j in range(len(rho)) if rho[j]==r]
         combinepart = []
         for j in indexset:
            combinepart += sigma[j]
         retsigma.append(combinepart)
         retrho.append(r)
         iSet = [j for j in iSet if j not in indexset]
         continue
      
      retsigma.append(sigma[i])
      retrho.append(rho[i])

   #print('so far we have '+str(retsigma)+' and '+str(retrho))
   #order after induced actions to get consecutive partitions
   retlistsort = sorted([[retsigma,retrho]],key = lambda x: x[1])
   
   #disentangle and reorder again
   csigma=[]
   crho = []
   for x in retlistsort:
      csigma.append(x[0])
      crho.append(x[1])
   
   if len(eq)==3:	#if info about choice function
      return((csigma,crho,eq[2]))      
   return((csigma,crho))

#routine to find reduce equilibria and remove duplicates

def equalpartition(part1,part2):
   for x in part1:
      if x not in part2:
         return(False)
   for x in part2:
      if x not in part1:
         return(False)
   return(True)

#duplicate eq; gives back whether two equilibria (partition and action profile) coincide or not
#the routine assumes an ordered action profile
def duplicate (eq1,eq2):
   sigma1,rho1 = eq1[0],eq1[1]
   sigma2,rho2 = eq2[0],eq2[1]
   
   length = len(rho1)
   
   if rho1 != rho2:
      return(False)
      
   for i in range(length):
      if not equalpartition(sigma1[i],sigma2[i]):
         return(False)
   return(True)

#clean equilibrium list by reducing it and removing duplicates
def cleanup (eqlis):
   redlis = list(map(lambda x: reduceeq(x), eqlis))
   #print('everything reduced')
   
   firsteq = redlis[0]
   returnlis = [firsteq]
   redlis = list(filter(lambda x: not duplicate(firsteq,x), redlis))
   
   while len(redlis) != 0:
      nexteq = redlis[0]
      returnlis.append(nexteq)
      redlis = list(filter(lambda x: not duplicate(nexteq,x), redlis))
      #print('The reduced list still has '+str(len(redlis))+' elements.')
   
   return(returnlis)

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

##equilibrium filter

def nonbabbling(eqlis):
   if len(eqlis[0])==3:
      print('The MLEU equilibrium contains the following non-babbling ones:')

   if len(eqlis[0])==2:
      print('The MEU equilibrium contains the following non-babbling ones:')
   
   return(list(filter(lambda x: len(x[1])!=1, eqlis)))




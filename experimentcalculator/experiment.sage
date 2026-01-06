reset()
from itertools import groupby, permutations, product
from operator import itemgetter
from typing import Any, Iterable, Tuple, List

#notifications - turn True for more info, turn False to suppress
notval = False
if not notval:
   print('Notifications are turned off.')
   #print('Note that notifications are turned off (wont complain about multiple maximizers). Turn them on by setting notval to True.')
reduceval = True
if reduceval:
   print('Solver applies the reduction lemma to simplify equilibria.')
   #print('Solver automatically applies the reduction lemma to reduce equilibria with different messages for the same action. To turn this off and find all pure equilibria, set reduceval to False.')

##sage-file for the equilibrium calculation within the experiment

#number of balls in the urn
Nballs = 10

#state space = number of red balls in unknown urn
Omega = [0,..,10]

#distribution (uniform)
P = [1/len(Omega) for x in Omega]

#number of balls drawn
K = 3

#set of histories (simplified for sufficient statistic), indicating the number of red balls observed (natural number)
H = [0,..,K]

#set of models (given h in H), a tuple of the numbers of observations 1. in favor, 2. in disfavor of a high number of red balls 
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
payoffs = [1300,1000,700,400,100,0]
while len(payoffs)<3*len(Omega):
   payoffs.append(0)

def posterior (relred, relblack):
   denom = sum([ P[ix] * (Omega[ix])^relred * (Nballs-Omega[ix])^relblack for ix in range(len(Omega))])
   if denom == 0:
      raise Exception('Probability zero event - denominator equals 0 and posterior update is formally undefined.')
   Pnew = [P[ix] * (Omega[ix])^relred * ((Nballs-Omega[ix]))^relblack / denom for ix in range(len(Omega))]
   return(Pnew)

def expectedpayoff (m,a,b=0):#of action a and bias b under model/relevant tuple m
   relred,relblack = m
   
   #updating the prior to the posterior
   Pnew = posterior(relred,relblack)
   
   util = sum([Pnew[i] * payoffs[abs(Omega[i]+b-a)] for i in range(len(Omega))])
   
   return(util)

#payoffmaximizer out of Omega given (the thought) relevant numbers of observed red and black balls, i.e. if receiver believes the narrative of the sender
def payoffmaximizer (relevanttuple,notifications=False): #model/tuple this is a(m,h,b) in the paper
   relred,relblack = relevanttuple
   
   #updating the prior to the posterior
   Pnew = posterior(relred,relblack)
   
   #payoffcheckloop
   baseutil = 0
   baseguess = Omega[0]
   baseguesslist = [baseguess]
   for x in Omega:		#the action 'test candidate' given the choice set to choose from
      
      #define receiver's utility function (bias b = 0)
      util = expectedpayoff(relevanttuple,x,0)
      
      if util == baseutil:
         #print('same utilitylevel occured')
         baseguesslist.append(x)
      
      if util > baseutil:
         baseutil = util
         baseguess = x
         baseguesslist = [x]
   if len(baseguesslist) > 1:
      if 5 not in baseguesslist:
         raise Exception('Multiple maximizers found, namely '+str(baseguesslist)+'. Dont know which maximizer to choose, as 5 is not one of them!')
      baseguess = 5
      if notifications:
         print('Note: Multiple maximizers found, namely '+str(baseguesslist)+' As the pooling action 5 is one of them, the program uses this action going forward.')
   return(baseguess)
   

#not needed currently
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

##
###auxiliary set functions (before equilibrium)
##


#takes the ordered set A = {a_1, a_2, ...} = {1,2,...} and gives back all monotone partitions, e.g., {0,1}, {2}, {3,4,...N-1}; by the monotonicity property of the reduction lemma, we use these as indexes (range(...)) for the sorted reduced list M of models
def monotonepartition (A):
   if len(A) == 0:
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

#
#MEU rule
#note that the history does not enter the function body, as the receiver does only worry about the worst-case model faced. Only implicitly, the history enters by ordering the models potentially differently.
def aMEU (mlis,h,notifications=False):
   atest = Omega[0]
   atestlis = [atest]
   valtest = min_symbolic([expectedpayoff(m,atest,0) for m in mlis])
   for a in Omega[1:]:
      valcomp = min_symbolic([expectedpayoff(m,a,0) for m in mlis])
      
      if valcomp == valtest:
         atestlis.append(a)
      
      if valcomp > valtest:
         atest = a
         atestlis = [atest]
         valtest = valcomp
   if notifications and len(atestlis) > 1:
      print('Multiple maximizers encountered, namely '+str(atestlis)+'. The program continues with '+str(atest)+'.')
   return(atest)
      
##
#MLEU
#

#define expected fit
#calculates the expected fit, i.e. the expected likelihood of observing h under narrative m
def expectedfit(m,h):
   s = m[0]+m[1] #number of relevant observations
   if K < s:
      raise Exception('narrative is longer than history')
   for elh in h:
      if elh not in [0,1]:
         raise Exception('history not consisting of 0s and 1s')
   k = m[1] #number of observations in favor of a high number
   
   fit = (1/2)^(K-s) * sum([ P[i] * (Omega[i]/len(Omega))^k * ((len(Omega)-Omega[i])/len(Omega))^(s-k)  for i in range(len(Omega))])   
   return(fit)

##
#Tiebreaker for MLEU
##

#takes a sorted(!) list (of (m, fit/value)) and iterates further for ties

def auxtie(pairs):
    pairs_sorted = sorted(pairs, key=itemgetter(1), reverse=True)

    groups = [list(g) for _, g in groupby(pairs_sorted, key=itemgetter(1))]

    group_perms = [list(permutations(g)) for g in groups]

    out = []
    for combo in product(*group_perms):
        out.append([item for group in combo for item in group])
    return out

   
#generate all tie-breakers
def tiebreakerlist (h,M):
   fitM = [(m,expectedfit(m,h)) for m in M]
   return(auxtie(fitM))
   #sortfitM = sorted(fitM,key = lambda mf: mf[1])
   

#define action with highest fit in a list of models under a history h, with ties broken according to a complete list tie
def aMLEU (mlis,h,tie):
   sortmlis = sorted([(m,expectedfit(m,h)) for m in mlis],key = lambda mf: mf[1])
   topmlis = list(filter(lambda x: x[1] == sortmlis[0][1], sortmlis))
   testmlis = [mf[0] for mf in topmlis]
   for m,fit in tie:
      if m in testmlis :
         return(payoffmaximizer(m))
   raise Exception('Unexpectedly, the model is not part of the tie-breaking rule!')
##

###
##generate set M of models considered (generically, this are all possible models), given a history (by means of the simplifying sufficient statistic)
###
def genMall (h):
   if K != len(h):
      raise Exception('Length of history ('+str(len(h))+') incompatible with expected one ('+str(K)+').')
   h0 = len([hi for hi in h if hi==0])
   h1 = K-h0
   
   M = []
   for n0 in [0..h0]:
      for n1 in [0..h1]:
         M.append((n0,n1)) 
   return(M)

def genMallnonempty (h): #generates all tuples of amounts of 0s and 1s that can be sent excluding the empty model
   return(list(filter(lambda x: x != (0,0), genMall(h))))


###eqcheck
##
#sigma = communication strategy = a partition of the set of models, rho = action taken in response to a partition by sigma, b = bias

#NOTE: the following function assumes that rho has already been constructed as the best reply of the receiver against sigma given an ambiguity rule, as is done in the equilibrium finder
def eqcheckinfinder (sigma,rho,b):
   for mlisi in range(len(sigma)):
      for m in sigma[mlisi]:
         maxEU = max_symbolic([expectedpayoff(m,rhoel,b) for rhoel in rho])
         if expectedpayoff(m,rho[mlisi],b) < maxEU:
            return(False)
   return(True)

#apply reduction lemma to reduce equilibria that induce the same action for different messages
def reduceeq(eq):
   sigma,rho = eq
from typing import Any, Iterable, Tuple, List

def reduceeq(
    eq: Tuple[List[Any], List[float]]
) -> Tuple[List[Any], List[float]]:
    
    sigma, rho = eq
    if len(sigma) != len(rho):
        raise ValueError("Both lists must have the same length.")

    acc = {}  # key: y-value, value: accumulated x
    for x, y in zip(sigma, rho):
        if y in acc:
            acc[y] = acc[y] + x
        else:
            acc[y] = x

    # dict preserves insertion order in Python 3.7+
    rho_reduced = list(acc.keys())
    sigma_reduced = list(acc.values())
    return sigma_reduced, rho_reduced

###
#remove equilibrium duplicates
def _freeze(eq):
    """Recursively convert lists (and tuples) into tuples so the result is hashable."""
    if isinstance(eq, list):
        return tuple(_freeze(x) for x in eq)
    if isinstance(eq, tuple):
        return tuple(_freeze(x) for x in eq)
    return eq

def remove_duplicates(eqlis):
    seen = set()
    out = []
    for eq in eqlis:
        key = _freeze(eq)
        if key not in seen:
            seen.add(key)
            out.append(eq)
    return out   
   
###
#equilibrium finder
##
def findeq(Mlis,h,b,type,reduceequilibria = reduceval):
   if type not in ['MLEU','MEU']:
      raise Exception('Equilibrium type ' + str(type) + ' you have given is undefined. Valid options are currently: MLEU, MEU.')
   
   ## MEU routine
   if type == 'MEU':
      ambrule = aMEU
   
      eqlis = []
      for sigma in monotonepartition(orderM(Mlis)):
         rho = [ambrule(mpart,h) for mpart in sigma]
         if eqcheckinfinder(sigma,rho,b):
            if reduceequilibria:
               sigma,rho = reduceeq((sigma,rho))
            eqlis.append((sigma,rho))
      #remove duplicates
      eqlis = remove_duplicates(eqlis)
   
   ## MLEU routine
   if type == 'MLEU':
      ambrule = aMLEU
      
      #initialize and iterate over tie-breaking rules
      tielis = tiebreakerlist(h,Mlis)
      eqlis = []
      for tie in tielis:
         eqtielis = []
         print('Equilibria for the tie-breaking rule '+str(tie)+': ')
         for sigma in monotonepartition(orderM(Mlis)):
            rho = [ambrule(mpart,h,tie) for mpart in sigma]
            if eqcheckinfinder(sigma,rho,b):
               if reduceequilibria:
                  sigma,rho = reduceeq((sigma,rho))
               eqtielis.append((sigma,rho))
         #remove duplicates
         eqtielis = remove_duplicates(eqtielis)
         print(eqtielis)
         eqlis.append(('Tie: '+str(tie),eqtielis))   
   return(eqlis)
###

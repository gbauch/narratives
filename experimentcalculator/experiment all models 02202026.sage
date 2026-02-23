reset()

#packages and tools loaded
import csv
from pathlib import Path
from itertools import groupby, permutations, product, cycle, combinations
from operator import itemgetter
from typing import Any, Iterable, Tuple, List
from sage.plot.colors import rainbow

#color palette
palette = cycle(rainbow(20))

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

#distribution (uniform)import csv
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


##closest to 5 finder
def closest25(lis):
   for el in lis:
      if el not in Omega:
         raise Exception('List '+str(lis)+'not a subset of '+str(Omega))
   baseaction = lis[0]
   baselis = [baseaction]
   for el in lis[1:]:
      if abs(5-el)<abs(5-baseaction):
         baseaction = el
         baselis = [baseaction]
         continue
      if abs(5-el)==abs(5-baseaction):
         baselis.append(el)
   if len(baselis) > 1:
      print('Multiple maximizers equally close to 5 found, namely '+str(baselis)+'. Program has chosen '+str(baseaction)+'.')
   return(baseaction)

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
   baseguess = Omega[0]
   baseguesslist = [baseguess]
   baseutil = expectedpayoff(relevanttuple,baseguess,0)
   for x in Omega[1:]:		#the action 'test candidate' given the choice set to choose from
      
      #define receiver's utility function (bias b = 0)
      util = expectedpayoff(relevanttuple,x,0)
      
      if util == baseutil:
         #print('same utilitylevel occured')
         baseguesslist.append(x)
         continue
      
      if util > baseutil:
         baseutil = util
         baseguess = x
         baseguesslist = [x]
   ##deactivated as we now have closest25
   #if len(baseguesslist) > 1:
   #   if 5 not in baseguesslist:
   #      raise Exception('Multiple maximizers found, namely '+str(baseguesslist)+'. Dont know which maximizer to choose, as 5 is not one of them!')
   #   baseguess = 5
   #   if notifications:
   #      print('Note: Multiple maximizers found, namely '+str(baseguesslist)+' As the pooling action 5 is one of them, the program uses this action going forward.')
   
   baseguess = closest25(baseguesslist)
   
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

#generates all options needed later for monotone partitions
def triplets(n):
    if n <0:
       raise Exception('Triplets have been given the negative number: '+str(n))
    return [(n-b-c, b, c) for b in [0, 1] for c in [0, 1] if n-b-c >= 0]

def powerset (lis):
   items = list(lis)
   for r in range(len(items) + 1):
      yield from combinations(items, r)

def partitions(s):
    items = list(s) #ensure it's a list
    if not items:
        yield []
        return

    first, rest = items[0], items[1:]
    for part in partitions(rest):
        # put `first` as a new block
        yield [[first]] + [block[:] for block in part]

        # or insert `first` into each existing block
        for i in range(len(part)):
            new_part = [block[:] for block in part]
            new_part[i].append(first)
            yield new_part


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

#takes into account ties via a function f : A -> R, via increasing f-values
#in case of a tie wrt f, it checks whether the elements are identical (-> no swap required) or are not (-> swap option desired)
#nevertheless procudes some duplicates, which get filtered later (-> not as efficient as it could be)
def monotonepartitionwrtf (A,f):

   #failsafe: sort A according to f
   A = sorted(A, key = f)
   
   if len(A) == 0:
      raise Exception('Empty set given')
      
   if len(A) == 1:
       yield [ A ]
       return
   
   #new idea: split according to f-equals and their elements - then go through all possibilities: front, middle, back and apply the iteration there. This creates some duplicates, namely, if front and middle are merged later on, but should reduce the complexity by a lot nevertheless
   
   
   #take next highest f-value (recall the list is ordered) and extract all equals and non-equals
   value = f(A[0])
   Afequal = [a for a in A if f(a) == value]
   Aremainder = [a for a in A if f(a) != value]
   
   #print('Afequal is '+str(Afequal))
   #print('Afremainder is '+str(Aremainder))
   
   #extract different actions involved and count them
   equalist = []
   for a in Afequal:
      if a not in equalist:
         equalist.append(a)
   #print(equalist)
   
   countalist = []
   for a in equalist:
      countalist.append((a, len([aa for aa in Afequal if aa == a])))
   
   #print('countalist is '+str(countalist))
   
   for aindex in range(len(equalist)):
      a = equalist[aindex]
      na = countalist[aindex][1]
      
      Anota = [aa for aa in A if aa != a]
      
      if len(Anota) == 0:
         yield [ [a for aa in range(na)] ]
         if na >=2:
            yield [ [a for aa in range(na-1)], [a] ] 
         
         continue
      
      for smaller in monotonepartitionwrtf(Anota, f):
         yield [ [a for aa in range(na)] ] + smaller
         yield [ [a for aa in range(na)] + smaller[0] ] + smaller[1:]
      
      if na >=2:
         for smaller in monotonepartitionwrtf([a]+Anota, f):
            yield [ [a for aa in range(na-1)] ] + smaller
   
"""
   if len(equalist) == 1:
      first = equalist[0]
      nfirst = countalist[0][1]
      if len(Aremainder) >=1:
         for smaller in monotonepartitionwrtf(Aremainder,f):
           yield [ [first for a in range(nfirst)] + smaller[0]] + smaller[1:] #fuse all firsts with new partition
           yield [ [first for a in range(nfirst) ]] + smaller #split away all firsts in new partition
           if nfirst >= 2:
              yield [ [first for a in range(nfirst-1) ]] + [[first]+smaller[0]] + smaller[1:] #split away all but one firsts in new partition
      
      if len(Aremainder) == 0:
         yield [ [first for a in range(nfirst)] ]
         if nfirst >=2:
            yield [ [first for a in range(nfirst -1)] ] + [[first]]
      
"""
"""
      
   if len(equalist) >= 2:
      produ = list(product(*[triplets(n) for a,n in countalist]))
      print('produ is '+str(produ))
   
      for p in produ:
         #print('produ is '+str(produ))
      
         Afront = []
         Amiddle = []
         Aback = []
         
         for aindex in range(len(equalist)):
            a = equalist[aindex]
            pa = p[aindex]
            
            print('pa is '+str(pa))
            for afrontnum in range(pa[0]):
               Afront.append(a)
            for amiddlenum in range(pa[1]):
               Amiddle.append(a)
            for abacknum in range(pa[2]):
               Aback.append(a)
      
      #print('Afront is '+str(Afront))
      #print('Amiddle is '+str(Amiddle))
      #print('Aback is '+str(Aback))
      
         if len(Afront) != 0:
            Afront = [Afront]
         if len(Amiddle) != 0:
            Amiddle = [Amiddle]
      #if len(Aback) != 0:
      #   Aback = [Aback]
         if len(Aremainder) == 0:
            if len(Aback)>=1:
               Aback = [Aback]
            print('Afront a is '+str(Afront))
            print('Amiddle a is '+str(Amiddle))
            print('Aback a is '+str(Aback))
            yield Afront + Amiddle + Aback
         
         if len(Aremainder) >= 1:
            for smaller in monotonepartitionwrtf(Aremainder, f):
               print('Afront is '+str(Afront))
               print('Amiddle is '+str(Amiddle))
               print('Aback is '+str(Aback))
               yield  Afront  +  Amiddle  + [Aback + smaller[0]] + smaller[1:]
"""

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
         continue
      
      if valcomp > valtest:
         atest = a
         atestlis = [atest]
         valtest = valcomp
   #if notifications and len(atestlis) > 1:
   #   print('Multiple maximizers encountered, namely '+str(atestlis)+'. The program continues with '+str(atest)+'.')
   
   atest = closest25(atestlis)
   
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
   
   fit = (1/2)^(K-s) * sum([ P[i] * (Omega[i]/(len(Omega)-1))^k * ((len(Omega)-1-Omega[i])/(len(Omega)-1))^(s-k)  for i in range(len(Omega))])   
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
   LL = auxtie(fitM)  
   def filter_tie_breakers_by_distance_to_center(L):
      ts = [tw[0] for tw in L]  # drop weights
      w = [tw[1] for tw in L]
      acts = [abs(payoffmaximizer(t, notifications=False)-5) for t in ts]
      return all(w[i] > w[i+1] or (acts[i] <= acts[i+1] and w[i] == w[i+1]) for i in range(len(acts) - 1))

   return [L for L in LL if filter_tie_breakers_by_distance_to_center(L)]
   

#define action with highest fit in a list of models under a history h, with ties broken according to a complete list tie
def aMLEU (mlis,h,tie=None):
   if tie == None:
      tie = tiebreakerlist(h,mlis)[0]
      print('No tie-breaker specified. Using '+str(tie)+'.')
   sortmlis = sorted([(m,expectedfit(m,h)) for m in mlis],key = lambda mf: -mf[1])
   topmlis = list(filter(lambda x: x[1] == sortmlis[0][1], sortmlis))
   testmlis = [mf[0] for mf in topmlis]
   for m,fit in tie:
      if m in testmlis:
         return(payoffmaximizer(m))
   raise Exception('Unexpectedly, the model is not part of the tie-breaking rule!')
##

###
##generate set M of models considered (generically, this are all possible models), given a history (by means of the simplifying sufficient statistic)
###
#February 17 2026: added to account for multiple occurences, e.g., if h=(1,0,1), there are two models that claim 1 relevant black and red ball
def genMallmultiple (h):
   if K != len(h):
      raise Exception('Length of history ('+str(len(h))+') incompatible with expected one ('+str(K)+').')
      
   part = powerset(h)
   M = []
   for el in part:
      M.append((len([h for h in el if h==1]), len([h for h in el if h==0])))
   return(M)

def genMall (h):
   if K != len(h):
      raise Exception('Length of history ('+str(len(h))+') incompatible with expected one ('+str(K)+').')
   h1 = len([hi for hi in h if hi==0]) #maximum number of relevant black balls
   h0 = K-h1 #maximum number of relevant black balls
   
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

#compares two m-lists
#check model by model whether it is in the other
def comparem (m1,m2):
   for m in m1:
      if m not in m2:
         return False
   for m in m2:
      if m not in m1:
         return False
   return True

def comparempart (mpart1, mpart2):
   if len(mpart1) != len(mpart2):
      return(False)
   for i in range(len(mpart1)):
      if not comparem(mpart1[i],mpart2[i]):
         return False
   return True

def sort_two_lists_by_second(data, reverse=False):
    out = []
    for first, second in data:
        if len(first) != len(second):
            raise ValueError("first_list and second_list must have the same length")

        pairs = sorted(zip(first, second), key=lambda t: t[1], reverse=reverse)

        if not pairs:  # leere Listen sauber behandeln
            out.append([[], []])
        else:
            first_sorted, second_sorted = map(list, zip(*pairs))
            out.append([first_sorted, second_sorted])
    return out


def remove_duplicates(eqlis):
   
   if len(eqlis) == 0:
      raise Exception('remove duplicates has been given an empty list!')
   
   #sort to ascending action profils
   eqlis = sort_two_lists_by_second(eqlis,False)
   
   
   #filter for duplicates in action profile   
   seen = [eqlis[0]]
   remlis = eqlis[1:]
   compeq = eqlis[0]
   
   while len(remlis) != 0:
      remlis = [eq for eq in remlis if (compeq[1] != eq[1] or not (comparempart(compeq[0],eq[0])))]
      
      if len(remlis) !=0:
         compeq = remlis[0]
         seen.append(compeq)
   return(seen)

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
      #for sigma in partitions(Mlis):
      #or #
      for sigma in monotonepartitionwrtf(Mlis,lambda m : payoffmaximizer(m)):
         rho = [ambrule(mpart,h) for mpart in sigma]
         if eqcheckinfinder(sigma,rho,b):
            #print('found equilibrium: '+str([sigma, rho]))
            if reduceequilibria:
               sigma,rho = reduceeq((sigma,rho))
            #if eqcheckmultiplemodels((sigma,rho)):
                  #print('Houston, I have found a problem. Check out '+str([sigma,rho]))
                  #raise Exception('Houston, I have found a problem. Check out '+str([sigma,rho]))
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
         #print('Equilibria for the tie-breaking rule '+str(tie)+': ')
         for sigma in partitions(order(Mlis)):
         #orämonotonepartitionwrtf(orderM(Mlis),lambda m : payoffmaximizer(m)):
            rho = [ambrule(mpart,h,tie) for mpart in sigma]
            if eqcheckinfinder(sigma,rho,b):
               if reduceequilibria:
                  sigma,rho = reduceeq((sigma,rho))
               if eqcheckmultiplemodels((sigma,rho)):
                  raise Exception('Houston, I have found a problem. Check out '+str([sigma,rho]))
               eqtielis.append((sigma,rho))
         #remove duplicates
         eqtielis = remove_duplicates(eqtielis)
         #print(eqtielis)
         eqlis.append(('Tie: '+str(tie),eqtielis))   
   return(eqlis)
###

###
#Manuel wanted to know why in the MEU equilibrium [[(0, 2)], [(0, 1), (1, 2), (0, 0), (1, 1)], [(1, 0)]], [1, 5, 8] there is a 5 as optimal action. Here comes a plot to illustrate that it depends on the expected utilities.

def testplotMEU(mlis,h):
   print('Action recommended by the program is aMEU = '+str(aMEU(mlis,h)))
   
   #prepare the graphic
   
   m0 = mlis[0]
   P = line([(a,expectedpayoff(m0,a)) for a in Omega],color=next(palette),legend_label=f""+str(m0))
   
   for m in mlis[1:]:
      P += line([(a,expectedpayoff(m,a)) for a in Omega],color=next(palette),legend_label=f""+str(m))
   
   return(show(P))
   



##write results in file
def write_equ(type,filt=False, csv_path=None):
    """
    Evaluate foo(x, y) for all pairs (x, y) from xs and ys and write results to a CSV.

    Parameters
    ----------
    foo : callable
        Function with signature foo(x, y).
    xs, ys : list
        Lists providing values for the first and second argument.
    csv_path : str | pathlib.Path
        Output CSV file path.
    header : tuple[str, str, str]
        Column names written as first row.
    """
    if type not in ['MEU','MLEU']:
       raise Exception('Type not of the form MEU or MLEU.')
    
    header=("h", "b", type)
    
    #generate output in one list with elements [h, b, eqlis], where eq = [sigma, rho]
    outlis = []
    
    
    #initialize hlis: could be made a lot simpler/compact:
    hlis = []
    for i in range(K+1):
       h=[]
       for j in range(i):
          h.append(1)
       while len(h) <K:
          h.append(0)
       hlis.append(h)
    print("List of histories: "+str(hlis))
    blis=[0,1,3]
    print('List of biases: '+str(blis))
    
    if csv_path is None:
        csv_path = Path.home() / "data.csv"   # z.B. /home/user/data.csv oder C:\Users\...\data.csv
    
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        if header:
            w.writerow(header)
        countb = 0
        for h in hlis:
            M = genMallmultiple(h)
            for b in blis:
               eqlis = findeq(M,h,b,type)
               if filt == True:
                  eqlis = eqfilter(eqlis)
                  #w.writerow(Filters applied)
               w.writerow([h, b, eqlis])
               
               outlis.append([h,b,eqlis])
               
               countb += 1/(len(hlis)*len(blis))
               print('Percentage done: '+str(numerical_approx(countb*100,digits=4))+'%')
    return(outlis)

#checks whether an equilibrium splits the same occurrence of two identical models; returns True in that case
def eqcheckmultiplemodels (eq):
   sigma = eq[0]
   for impart in range(len(sigma)):
      mpart = sigma[impart]
      for m in mpart:
         for mpartrem in sigma[impart+1:]:
            if m in mpartrem:
               #print('Equilibrium split occured. mpart is '+str(mpart)+'. m is '+str(m)+'. and mpartrem is '+str(mpartrem))
               return(True)
   return(False)

#filter according to assumptions
def eqfilter (eqlis):
   #filter for most informative equilibrium
   maxN = max_symbolic([len(eq[1]) for eq in eqlis])
   eqlis = [eq for eq in eqlis if len(eq[1])==maxN]
   
   #filter for action profile dominance; if undominated, add to new list
   eqlisnew = []
   for eq in eqlis:
      rho = eq[1]
      add_value = True
      for eqrem in eqlis:
         rhocomp = eqrem[1]
         if (len([i for i in range(len(rho)) if rho[i] <= rhocomp[i]])==len(rho)) & (len([i for i in range(len(rho)) if rho[i] < rhocomp[i]])>=1) :
            add_value = False
            break
      if add_value:
         eqlisnew.append(eq)
   eqlis = eqlisnew
   
   return(eqlis)

#
#Deltas-Definition
#
#blow up equilibria form sufficient statistic to subset of relevant
def blow_up_eq(h,b,eq):
   M = genMallmultiple(h)
   print('perhaps not needed')



#Manuel's selection criterion
def selection (Mtilde, b):
   
   mvallis = [Mtilde[0]]
   val = min_symbolic([expectedpayoff(Mtilde[0],payoffmaximizer(mm), b) for mm in Mtilde])
   
   for m in Mtilde[1:] :
      valtest = min_symbolic([expectedpayoff(m,payoffmaximizer(mm), b) for mm in Mtilde])
      
      if val == valtest:
         mvallis.append(m)
         
      if valtest > val:
         mvallis = [m]
         val = valtest
   
   if len(mvallis)==1:
      return(mvallis[0])
   
   if notval:
      print('Multiple selections possible, namely, mvallis = '+str(mvallis))
   return(mvallis[0]) #sorted(mvallis, key = lambda m : closest25(payoffmaximizer(m)))[0]
   
   
def Deltahb (h,b,filtered = False):
   if (len(h) != 3) or (b not in [0,1,2,3]) or (len([el for el in h if el in [0,1]])!=3):
      raise Excepiton('Deltamhb was given an invalid input. Input was (m,h,b) =  '+str(m,h,b))
   
   #M = genMallmultiple(h)
   #if m not in M:
   #   raise Exception('Given model m = '+str(m)+ 'not in the set of models generated by h, namely M = '+str(M))

   if filtered:
      eqlist = filteredlist
   if not filtered:
      eqlist = unfilteredlist
   
   
   #find the list equilibria corresponding to h,b, check whether its unique as a failsafe
   Gammahbpre = list(filter(lambda x : (x[0],x[1]) == (h, b) , eqlist))
   if len(Gammahbpre) != 1:
      raise Exception('Expected unique equilibrium list, but got the following: '+str(Gammahbpre))
   
   #print('Gammahbpre = '+str(Gammahbpre))
   Gammahb = Gammahbpre[0][2] #list(filter(lambda x : (x[0],x[1]) == (h, b) , eqlist[0][2]))
   
   
   #print('I expect to find 8 = '+str(sum([len(part) for part in Gammahb[0][0]])))
   
   s = 0
   for sigma, rho in Gammahb:
      #print('sigma, rho = '+str((sigma,rho)))
      for partindex in range(len(sigma)):
         part = sigma[partindex]
         action = rho[partindex]
         for m in part:
            s+= (payoffmaximizer(selection(part, b)) - action)      
   ret = s/(len(Gammahb* sum([len(part) for part in Gammahb[0]])))
   print('Delta is '+str(ret)+', numerically '+str(numerical_approx(ret, digits = 4)))
   return(ret)
   
   













filteredlist = [[[0, 0, 0],
  0,
  [[[[(0, 2), (0, 2), (0, 2), (0, 3)], [(0, 1), (0, 1), (0, 1)], [(0, 0)]],
    [1, 2, 5]]]],
 [[0, 0, 0],
  1,
  [[[[(0, 2), (0, 2), (0, 2), (0, 3), (0, 1), (0, 1), (0, 1)], [(0, 0)]],
    [2, 5]]]],
 [[0, 0, 0],
  3,
  [[[[(0, 2), (0, 2), (0, 2), (0, 3), (0, 1), (0, 1), (0, 1), (0, 0)]], [4]]]],
 [[1, 0, 0],
  0,
  [[[[(0, 2)], [(0, 1), (0, 1)], [(1, 2)], [(0, 0), (1, 1), (1, 1)], [(1, 0)]],
    [1, 2, 4, 5, 8]]]],
 [[1, 0, 0],
  1,
  [[[[(0, 2), (0, 1), (0, 1)], [(1, 2), (0, 0), (1, 1), (1, 1)], [(1, 0)]],
    [2, 5, 8]]]],
 [[1, 0, 0],
  3,
  [[[[(0, 2), (0, 1), (0, 1), (1, 2), (0, 0), (1, 1), (1, 1), (1, 0)]], [5]]]],
 [[1, 1, 0],
  0,
  [[[[(0, 1)], [(0, 0), (1, 1), (1, 1)], [(2, 1)], [(1, 0), (1, 0)], [(2, 0)]],
    [2, 5, 6, 8, 9]]]],
 [[1, 1, 0],
  1,
  [[[[(0, 1)], [(0, 0), (1, 1), (1, 1)], [(2, 1), (1, 0), (1, 0), (2, 0)]],
    [2, 5, 7]],
   [[[(0, 1)], [(0, 0)], [(1, 1), (1, 1), (2, 1), (1, 0), (1, 0), (2, 0)]],
    [2, 5, 7]],
   [[[(0, 1)], [(0, 0), (1, 1)], [(1, 1), (2, 1), (1, 0), (1, 0), (2, 0)]],
    [2, 5, 7]]]],
 [[1, 1, 0],
  3,
  [[[[(0, 1), (0, 0), (1, 1), (1, 1), (2, 1), (1, 0), (1, 0), (2, 0)]], [5]]]],
 [[1, 1, 1],
  0,
  [[[[(0, 0)], [(1, 0), (1, 0), (1, 0)], [(2, 0), (2, 0), (2, 0), (3, 0)]],
    [5, 8, 9]]]],
 [[1, 1, 1],
  1,
  [[[[(0, 0)], [(1, 0), (1, 0), (1, 0), (2, 0), (2, 0), (2, 0), (3, 0)]],
    [5, 8]]]],
 [[1, 1, 1],
  3,
  [[[[(0, 0), (1, 0), (1, 0), (1, 0), (2, 0), (2, 0), (2, 0), (3, 0)]], [6]]]]]

unfilteredlist = [[[0, 0, 0],
  0,
  [[[[(0, 2), (0, 2), (0, 2), (0, 3)], [(0, 1), (0, 1), (0, 1)], [(0, 0)]],
    [1, 2, 5]],
   [[[(0, 2), (0, 2), (0, 2), (0, 3), (0, 1), (0, 1), (0, 1)], [(0, 0)]],
    [2, 5]],
   [[[(0, 2), (0, 2), (0, 2), (0, 3), (0, 1), (0, 1), (0, 1), (0, 0)]], [4]]]],
 [[0, 0, 0],
  1,
  [[[[(0, 2), (0, 2), (0, 2), (0, 3), (0, 1), (0, 1), (0, 1)], [(0, 0)]],
    [2, 5]],
   [[[(0, 2), (0, 2), (0, 2), (0, 3)], [(0, 1), (0, 1), (0, 1), (0, 0)]],
    [1, 5]],
   [[[(0, 2), (0, 2), (0, 2), (0, 3), (0, 1), (0, 1), (0, 1), (0, 0)]], [4]],
   [[[(0, 3)], [(0, 2), (0, 2), (0, 2), (0, 1), (0, 1), (0, 1), (0, 0)]],
    [1, 4]]]],
 [[0, 0, 0],
  3,
  [[[[(0, 2), (0, 2), (0, 2), (0, 3), (0, 1), (0, 1), (0, 1), (0, 0)]], [4]]]],
 [[1, 0, 0],
  0,
  [[[[(0, 2)], [(0, 1), (0, 1)], [(1, 2)], [(0, 0), (1, 1), (1, 1)], [(1, 0)]],
    [1, 2, 4, 5, 8]],
   [[[(0, 2), (0, 1), (0, 1)], [(1, 2)], [(0, 0), (1, 1), (1, 1)], [(1, 0)]],
    [2, 4, 5, 8]],
   [[[(0, 2)], [(0, 1), (0, 1), (1, 2)], [(0, 0), (1, 1), (1, 1)], [(1, 0)]],
    [1, 3, 5, 8]],
   [[[(0, 2), (0, 1), (0, 1), (1, 2)], [(0, 0), (1, 1), (1, 1)], [(1, 0)]],
    [3, 5, 8]],
   [[[(0, 2)], [(0, 1), (0, 1)], [(1, 2), (0, 0), (1, 1), (1, 1)], [(1, 0)]],
    [1, 2, 5, 8]],
   [[[(0, 2), (0, 1), (0, 1)], [(1, 2), (0, 0), (1, 1), (1, 1)], [(1, 0)]],
    [2, 5, 8]],
   [[[(0, 2), (0, 1), (0, 1), (1, 2), (0, 0)], [(1, 1), (1, 1)], [(1, 0)]],
    [4, 5, 8]],
   [[[(0, 2), (0, 1), (0, 1), (1, 2), (0, 0), (1, 1), (1, 1)], [(1, 0)]],
    [4, 8]],
   [[[(0, 2)], [(0, 1), (0, 1)], [(1, 2)], [(0, 0), (1, 1), (1, 1), (1, 0)]],
    [1, 2, 4, 5]],
   [[[(0, 2), (0, 1), (0, 1)], [(1, 2)], [(0, 0), (1, 1), (1, 1), (1, 0)]],
    [2, 4, 5]],
   [[[(0, 2)], [(0, 1), (0, 1), (1, 2)], [(0, 0), (1, 1), (1, 1), (1, 0)]],
    [1, 3, 5]],
   [[[(0, 2), (0, 1), (0, 1), (1, 2)], [(0, 0), (1, 1), (1, 1), (1, 0)]],
    [3, 5]],
   [[[(0, 2)], [(0, 1), (0, 1)], [(1, 2), (0, 0), (1, 1), (1, 1), (1, 0)]],
    [1, 2, 5]],
   [[[(0, 2), (0, 1), (0, 1)], [(1, 2), (0, 0), (1, 1), (1, 1), (1, 0)]],
    [2, 5]],
   [[[(0, 2), (0, 1), (0, 1), (1, 2), (0, 0), (1, 1), (1, 1), (1, 0)]], [5]]]],
 [[1, 0, 0],
  1,
  [[[[(0, 2), (0, 1), (0, 1)], [(1, 2), (0, 0), (1, 1), (1, 1)], [(1, 0)]],
    [2, 5, 8]],
   [[[(0, 2)], [(0, 1), (0, 1), (1, 2), (0, 0), (1, 1), (1, 1)], [(1, 0)]],
    [1, 5, 8]],
   [[[(0, 2), (0, 1), (0, 1), (1, 2), (0, 0), (1, 1), (1, 1)], [(1, 0)]],
    [4, 8]],
   [[[(0, 2), (0, 1), (0, 1)], [(1, 2), (0, 0)], [(1, 1), (1, 1), (1, 0)]],
    [2, 5, 7]],
   [[[(0, 2)], [(0, 1), (0, 1), (1, 2), (0, 0)], [(1, 1), (1, 1), (1, 0)]],
    [1, 5, 7]],
   [[[(0, 2), (0, 1), (0, 1)], [(1, 2), (0, 0), (1, 1), (1, 1), (1, 0)]],
    [2, 5]],
   [[[(0, 2)], [(0, 1), (0, 1), (1, 2), (0, 0), (1, 1), (1, 1), (1, 0)]],
    [1, 5]],
   [[[(0, 2), (0, 1), (0, 1), (1, 2), (0, 0), (1, 1), (1, 1), (1, 0)]], [5]],
   [[[(0, 2), (0, 1), (0, 1)], [(1, 2), (0, 0), (1, 1)], [(1, 1), (1, 0)]],
    [2, 5, 7]],
   [[[(0, 2)], [(0, 1), (0, 1), (1, 2), (0, 0), (1, 1)], [(1, 1), (1, 0)]],
    [1, 5, 7]]]],
 [[1, 0, 0],
  3,
  [[[[(0, 2), (0, 1), (0, 1), (1, 2), (0, 0), (1, 1), (1, 1), (1, 0)]], [5]]]],
 [[1, 1, 0],
  0,
  [[[[(0, 1)], [(0, 0), (1, 1), (1, 1)], [(2, 1)], [(1, 0), (1, 0)], [(2, 0)]],
    [2, 5, 6, 8, 9]],
   [[[(0, 1), (0, 0), (1, 1), (1, 1)], [(2, 1)], [(1, 0), (1, 0)], [(2, 0)]],
    [5, 6, 8, 9]],
   [[[(0, 1)], [(0, 0), (1, 1), (1, 1), (2, 1)], [(1, 0), (1, 0)], [(2, 0)]],
    [2, 5, 8, 9]],
   [[[(0, 1), (0, 0), (1, 1), (1, 1), (2, 1)], [(1, 0), (1, 0)], [(2, 0)]],
    [5, 8, 9]],
   [[[(0, 1)], [(0, 0), (1, 1), (1, 1)], [(2, 1), (1, 0), (1, 0)], [(2, 0)]],
    [2, 5, 7, 9]],
   [[[(0, 1), (0, 0), (1, 1), (1, 1)], [(2, 1), (1, 0), (1, 0)], [(2, 0)]],
    [5, 7, 9]],
   [[[(0, 1)], [(0, 0), (1, 1), (1, 1)], [(2, 1)], [(1, 0), (1, 0), (2, 0)]],
    [2, 5, 6, 8]],
   [[[(0, 1), (0, 0), (1, 1), (1, 1)], [(2, 1)], [(1, 0), (1, 0), (2, 0)]],
    [5, 6, 8]],
   [[[(0, 1)], [(0, 0), (1, 1), (1, 1), (2, 1)], [(1, 0), (1, 0), (2, 0)]],
    [2, 5, 8]],
   [[[(0, 1), (0, 0), (1, 1), (1, 1), (2, 1)], [(1, 0), (1, 0), (2, 0)]],
    [5, 8]],
   [[[(0, 1)], [(0, 0), (1, 1), (1, 1)], [(2, 1), (1, 0), (1, 0), (2, 0)]],
    [2, 5, 7]],
   [[[(0, 1), (0, 0), (1, 1), (1, 1)], [(2, 1), (1, 0), (1, 0), (2, 0)]],
    [5, 7]],
   [[[(0, 1)], [(0, 0), (1, 1), (1, 1), (2, 1), (1, 0), (1, 0), (2, 0)]],
    [2, 6]],
   [[[(0, 1), (0, 0), (1, 1), (1, 1), (2, 1), (1, 0), (1, 0), (2, 0)]], [5]],
   [[[(0, 1)], [(1, 1), (1, 1)], [(0, 0), (2, 1), (1, 0), (1, 0), (2, 0)]],
    [2, 5, 6]]]],
 [[1, 1, 0],
  1,
  [[[[(0, 1)], [(0, 0), (1, 1), (1, 1)], [(2, 1), (1, 0), (1, 0), (2, 0)]],
    [2, 5, 7]],
   [[[(0, 1), (0, 0), (1, 1), (1, 1)], [(2, 1), (1, 0), (1, 0), (2, 0)]],
    [5, 7]],
   [[[(0, 1)], [(0, 0)], [(1, 1), (1, 1), (2, 1), (1, 0), (1, 0), (2, 0)]],
    [2, 5, 7]],
   [[[(0, 1), (0, 0)], [(1, 1), (1, 1), (2, 1), (1, 0), (1, 0), (2, 0)]],
    [5, 7]],
   [[[(0, 1)], [(0, 0), (1, 1), (1, 1), (2, 1), (1, 0), (1, 0), (2, 0)]],
    [2, 6]],
   [[[(0, 1), (0, 0), (1, 1), (1, 1), (2, 1), (1, 0), (1, 0), (2, 0)]], [5]],
   [[[(0, 1)], [(0, 0), (1, 1)], [(1, 1), (2, 1), (1, 0), (1, 0), (2, 0)]],
    [2, 5, 7]],
   [[[(0, 1), (0, 0), (1, 1)], [(1, 1), (2, 1), (1, 0), (1, 0), (2, 0)]],
    [5, 7]]]],
 [[1, 1, 0],
  3,
  [[[[(0, 1), (0, 0), (1, 1), (1, 1), (2, 1), (1, 0), (1, 0), (2, 0)]], [5]]]],
 [[1, 1, 1],
  0,
  [[[[(0, 0)], [(1, 0), (1, 0), (1, 0)], [(2, 0), (2, 0), (2, 0), (3, 0)]],
    [5, 8, 9]],
   [[[(0, 0)], [(1, 0), (1, 0), (1, 0), (2, 0), (2, 0), (2, 0), (3, 0)]],
    [5, 8]],
   [[[(0, 0), (1, 0), (1, 0), (1, 0), (2, 0), (2, 0), (2, 0), (3, 0)]], [6]]]],
 [[1, 1, 1],
  1,
  [[[[(0, 0)], [(1, 0), (1, 0), (1, 0), (2, 0), (2, 0), (2, 0), (3, 0)]],
    [5, 8]],
   [[[(0, 0), (1, 0), (1, 0), (1, 0), (2, 0), (2, 0), (2, 0), (3, 0)]], [6]]]],
 [[1, 1, 1],
  3,
  [[[[(0, 0), (1, 0), (1, 0), (1, 0), (2, 0), (2, 0), (2, 0), (3, 0)]], [6]]]]]

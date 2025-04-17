
from sage.symbolic.integration.integral import indefinite_integral

###
##set operations
###

#from https://stackoverflow.com/questions/19368375/set-partitions-in-python
def partitions(collection):  #creates the set of all partitions of a set of models M
    if len(collection) == 1:
        yield [ collection ]
        return

    first = collection[0]
    for smaller in partitions(collection[1:]):
        # insert `first` in each of the subpartition's subsets
        for n, subset in enumerate(smaller):
            yield smaller[:n] + [[ first ] + subset]  + smaller[n+1:]
        # put `first` in its own subset 
        yield [ [ first ] ] + smaller

def monotonepartition (A):   #takes the ordered set A = {a_1, a_2, ...} = {1,2,...} and gives back all monotone partitions, e.g. {0,1}, {2}, {3,4,...N-1}; by the monotonicity property of the reduction lemma, we use these as indexes (range(...)) for the sorted reduced list M of models
   if len(A) ==0:
      raise Exception('Empty set given')
   if len(A) == 1:
       yield [ A ]
       return
   
   first = A[0]
   for smaller in monotonepartition(A[1:]):
      yield [ [first] + smaller[0]] + smaller[1:]
      yield [ [first] ] + smaller 

def testcount (N): # just for me to check whether the above does what it is supposed to do
   if N==1:
      return 1
   return 1 + sum([testcount(i) for i in [1..(N-1)]])

def power (ls):		#creates the powerset as a list
   return(list(powerset(ls)))

def nonemptypower (ls):  #creates the powerset and takes out the empty set
   return(list(filter(lambda x: x != [],powerset(ls))))



def subseteq (A,B): #checks if A is a subset of B
   for a in A:
      if a not in B:
         return(False)
   return(True)

#from https://stackoverflow.com/questions/952914/how-do-i-make-a-flat-list-out-of-a-list-of-lists
def flatten(xss):		#flattens a list; will be needed to undo the reduced set of models rM
    return [x for xs in xss for x in xs]


###
##generate set M of models
###

#Models m now have the form (n0,n1) - numbers of 0s and 1s credited

def genMall (h): #generates all tuples of amounts of 0s and 1s that can be sent
   K = len(h)
   h0 = len([hi for hi in h if hi==0])
   h1 = K-h0
   
   M = []
   for n0 in [0..h0]:
      for n1 in [0..h1]:
         M.append((n0,n1)) 
   
   return(M)

def genMallnonempty (h): #generates all tuples of amounts of 0s and 1s that can be sent excluding the empty model
   return(list(filter(lambda x: x != (0,0), genMall(h))))


def genMcut (h): #generates all models given cutoff strategies (Schwarzstein, Sunderam AER 2021)
   K = len(h)
   M = []
   for k in range(K+1):  #ignores the empty model; to add allow k=K
      newh = h[k:]
      new1 = sum(newh)
      M.append((K-k-new1,new1))
   return(M)

def genMcutnonempty (h): #generates all models given cutoff strategies (Schwarzstein, Sunderam AER 2021) excluding the empty model
   K = len(h)
   M = []
   for k in range(K):  #ignores the empty model; to add allow k=K
      newh = h[k:]
      new1 = sum(newh)
      M.append((K-k-new1,new1))
   return(M)

###
##Exception catchers
###
def checkh (h): #checks if a history is valid
   if len(h)==0:
      raise Exception('History of empty length given.')
   for hi in h:
      if hi not in [0,1]:
         raise Exception('History given ('+str(h)+') is not a valid history.')

def checkb (b): #checks if b is a real number
   if not b in RR:
      raise Exception('Given b ('+str(b)+') is not a real number')

def checkMh (M,h): #checks if M is a list of with h compatible models
   K = len(h)
   Klis = list(range(K))
   for m0,m1 in M:
      if m0+m1>K:
         raise Exception('The model '+str(m)+' is not a valid model featured in the estimated range '+str(Klis))

def checkall(h,b,M):
   checkh(h)
   checkb(b)
   checkMh(M,h)

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
   checkMh(M,h)
   #need to sort this here!
   ml = sorted([(m, likelihood(m,h)) for m in M],key = lambda tup: -tup[1]) #sort models by decreasing likelihood
   return(choicegen(ml))

def choicefunction (mlis, cml):		#selects the model m from cmlis according to the model-likelihood list / choice function ml
   for x in cml:
      if x[0] in mlis:
         return(x[0])   


def emptylikelilast (cml):		#checks whether the empty message is ranked last within its likelihood
   #identify occurence of m=(0,0)
   for i in range(len(cml)):
      if cml[i][0] == (0,0):
         vlik = cml[i][1]
         j = i
         break
   for (m,lik) in cml[j+1:]:
      if lik ==vlik:
         return(False)
   return(True)
         


##
def Nstagecheck(eqlis):
   Nstagelis=[]
   for eq in eqlis:
      avec = eq[1]
      
      #check for duplicates (=> can avoid them by the reduction lemma b; inform me when that happens)
      nodoubles=[]
      for x in avec:
         if x in nodoubles:
            print('Duplicate actions found; you might want to reduce them by the reduction lemma part b before going on. Here is the duplicate found:')
            print(eq)
            #raise Exception('Duplicate actions found; you might want to reduce them by the reduction lemma part b before going on.')
            
         if x not in nodoubles:
            nodoubles.append(x)
      
      N = len(nodoubles)
      if N not in Nstagelis:
         Nstagelis.append(N)
   
   sort=sorted(Nstagelis)
   
   if sort[len(sort)-1]==len(sort):
      return(True)
   #print('Equilibrium given does not fullfill the Nstage-property:')
   return(False)      
      
def Hlis (K):
   #creates a representative list of all sufficient h elements
   ret = []
   for k in range(K+1):
      ret.append([0 for i in range(k)]+[1 for i in range(K-k)])
   return(ret)
   
def lineplot (ls):
   P = points([(0,0)])
   for i in range(len(ls)-1):
      P+=line([ls[i],ls[i+1]])
   return(show(P))
   
   




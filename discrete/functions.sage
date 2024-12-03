
##
#implements functions related to the example (uniform quadratic, parabolas, likelihood etc.)
##

#assuming uniform prior on [0,1] (could be changed)
f0(theta) = 1

def posterior (m,h):		#returns the CDF, PDF, mean and variance as a vector   
   checkMh([m],h)
   K = len(h)   	#length of history
   s = m[0]+m[1] 	#number of claimed relevant states
   k = m[1]		#number of claimed hits
   
   assume(0<=theta<=1)
   f(theta) = (f0(theta) * theta^k*(1-theta)^(s-k) / (integral(f0(x) * x^k*(1-x)^(s-k), (x,0,1))) ).full_simplify()
   F(theta) = (integral(f(x),(x,0,theta))).full_simplify()
   
   mean = integral(theta * f(theta),(theta,0,1))
   variance = integral(theta^2 * f(theta),(theta,0,1)) - mean^2
   
   return([F(theta),f(theta),mean,variance])

def quickmean (m,h):		#based on the formula for the beta distribution
   s = m[0]+m[1]
   K = len(h)
   k = m[1]
   return((k+1)/(s+2))

def quickmeanvar (m,h):		#based on the formula for the beta distribution
   s = m[0]+m[1]
   K = len(h)
   k = m[1]
   return([(k+1)/(s+2),(k+1)*(s-k+1)/((s+2)^2 * (s+3))])


def utility (m,h):
   (mean, var) = quickmeanvar(m,h)
   return((-(theta-mean)^2 - var).full_simplify())

def parabola (mv):
   mean = mv[0]
   var = mv[1]
   return((-(theta-mean)^2 - var).expand())

   
def intersection (aa,bb):
   #parabolas of the form -(theta -bi)^2-ci
   [b1,c1] = aa
   [b2,c2] = bb
   
   if b1 == b2:
      #if c1 == c2:
      #   return([b1,c1])
      return([b1,min_symbolic([-c1,-c2])])
   
   mid = (b1+b2)/2 - (c2-c1)/(2*(b1-b2))
   value = -(mid-b1)^2-c1
   value2 = -(mid-b2)^2-c2
   if value != value2:
      raise Exception('Big problem, values dont agree in intersection!')
   return([mid,value])


def biasedutility (b,m,h):
   (mean, var) = quickmeanvar(m,h)
   return((-(theta-mean-b)^2 - var).full_simplify())

##
#calculates the likelihood of observing h under narrative m
def likelihood(m,h):
   K = len(h)
   s = m[0]+m[1]
   if K < s:
      raise Exception('narrative is longer than history')
   for elh in h:
      if elh not in [0,1]:
         raise Exception('history not consisting of 0s and 1s')
   k = m[1]
   
   like = (1/2)^(K-s) * integral( theta^k * (1-theta)^(s-k) * f0(theta), (theta,0,1))
   
   return(like)
   


###
#reduction functions
#check reduction lemma
###

def reducemodels (M,h):  #reduces the number of models considered via the monotonicity property of the reduction lemma (they will induce the same action)
   meanlis = [quickmean(m, h) for m in M]
   strokelis = copy(meanlis)
   reducedMwithmean = [] #collects tuples of 1. list of models m leading to the same mean/action 2. their mean to later sort them accordingly
   for i in range(len(M)):
      if meanlis[i] in strokelis:
         reducedMwithmean.append(([M[j] for j in range(len(M)) if meanlis[j] == meanlis[i]], meanlis[i]))
         strokelis = list(filter(lambda x: x != meanlis[i], strokelis))
   
   #sort reducedMwithmean by mean
   sortreducedM = sorted(reducedMwithmean,key = lambda tup: tup[1])
   
   retM = [tup[0] for tup in sortreducedM]   
   return(retM)

def simplifyeq (P, avec): #merges messages with the same induced action, creating a new, normalized equilibrium (cf. reduction lemma)
   return('not implemented yet')




###
#search/action functions
###


def findlikeli (mlis, h):
   if len(mlis) == 0:
      raise Exception('Empty narrative list given!')   
   
   likelisall = [[m, likelihood(m,h)] for m in mlis]
   valis = [tup[1] for tup in likelisall]
   #print(likelisall)
   val = valis[0]
   for v in valis:
      if v > val:
         val = v
   
   likelis = list(filter(lambda x: x[1]==val,likelisall))
   
   ##tie-breaking rule (need to include b for sender preferred) - for now just take first element
   ret = quickmeanvar(likelis[0][0],h)

   return([ret[0],-ret[1]])

def findlikelichoice (mlis, h, cml):
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
   ret = quickmeanvar(choicefunction(likelis, cml),h)

   return([ret[0],-ret[1]])

   

###not optimal, but works
def findmode (mlis, h):
   if len(mlis) == 0:
      raise Exception('Empty narrative list given!')
   
   
   meanvarlis = [quickmeanvar(m,h) for m in mlis]

   pointlis = []
   for tup in meanvarlis:
      for tupp in meanvarlis:
         pointlis.append(intersection(tup,tupp)[0])
   
   #print('Pointlis is '+str(pointlis))

   newm = pointlis[0]
   newv = min_symbolic([parabola(quickmeanvar(m,h)).subs(theta=pointlis[0]) for m in mlis])
   
   for poi in pointlis:
      mincomp = min_symbolic([parabola(quickmeanvar(m,h)).subs(theta=poi) for m in mlis])
      
      if mincomp > newv:
         newm = poi
         newv = mincomp
   
   return([newm,newv])

def optimalmaxminaction (h,p):
   ret = []
   for M in p:
      ret.append(findmode(M,h)[0])
   return(ret)

def optimallikeliaction (h,p):
   a = []
   for M in p:
      a.append(findlikeli(M,h)[0])
   return(a)

def optimallikeliactionchoice (h,p,cml):
   a = []
   for M in p:
      a.append(findlikelichoice(M,h,cml)[0])
   return(a)

def senderoptimal(h,p,a,b):
   if len(p) != len(a):
      raise Exception('partition and action vector have different dimensions')
   for i in range(len(p)):
      for m in p[i]:
         expstate = quickmeanvar(m,h)[0]
         #somehow, sage really doesnt like comparisons for elaborate expressions, so do the checks otherwise
         if abs(expstate + b - a[i]) > min_symbolic([abs(expstate + b - ael) for ael in a]):
            return(False)
   return(True)


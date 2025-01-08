reset()

###
#Best guess and expected number of balls in the experiment
###


#aux
def closestint (x):
   flx = floor(x)
   if abs(x-flx)<abs(flx+1-x):
      return(flx)
   if abs(x-flx)>abs(flx+1-x):
      return(flx+1)
   print('funny - it is exactly x.5! - The floored number is used in the following..')
   return(flx)
###

X = [1..9]			#(restricted) possible numbers of red balls out of 10
P = [1/len(X) for x in X]	#uniform distribution of scenarios

payoffs = [10,7,2]
while len(payoffs)<len(X):
   payoffs.append(0)


def payoffmaximizer (relred,relblack):	#payoffmaximizer out of [1..10] given (thought) relevant numbers of observed red and black balls
   
   #updated posterior (see the next function for more documentation)
   denom = sum([ P[ix] * (X[ix])^relred * (10-X[ix])^relblack for ix in range(len(X))])
   Pnew = [P[ix] * (X[ix])^relred * ((10-X[ix]))^relblack / denom for ix in range(len(X))]
   
   #payoffcheckloop
   baseutil = 0
   baseguess = X[0]
   for x in X:		#the 'test candidate'
      
      util = 0
      for iy in range(len(X)):	#looping through all true possibilities
         y=X[iy]
         util += Pnew[iy] * payoffs[abs(x-y)]
      
      if util > baseutil:
         baseutil = util
         baseguess = x
   
   return(baseguess)
   

def expectednumber (relred,relblack):
   #we need to calculate the updated probability
   
   #denominator for the updates: overall probability of making the above (relevant) observation - note that we neglect the binomial coefficient, as it factors out anyway and I don't know on the fly which one it is
   #of course, one could also leave out the divisions by 10...
   denom = sum([ P[ix] * (X[ix]/10)^relred * ((10-X[ix])/10)^relblack for ix in range(len(X))])
   
   Pnew = []
   for ix in range(len(X)):
      x = X[ix]
      #prob of seeing the numbers if x is describes the true decompositions
      ret = P[ix] * (x/10)^relred * ((10-x)/10)^relblack / denom
      Pnew.append(ret)
   
   #check
   if sum(Pnew) != 1:
      raise Exception('Houston!')
   #print([numerical_approx(el) for el in Pnew])
   
   #the expected number is closest element of X to the updated expectation
   realnumber = sum([Pnew[ix]*X[ix] for ix in range(len(X))])
   print('real number would be '+str(numerical_approx(realnumber,digits=4))+' - the rounded number is thus:')
   return(closestint(realnumber))

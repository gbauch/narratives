
##this file is written to cope with the *sufficient statistics* of the example (how many 0s, 1s in a certain length)

##
#new meta
##

#an element m of M is a tuple (n0,n1) counting the numbers of 0s and 1s deemed relevant

reset()
load("auxiliary.sage") #auxiliary functions
load("functions.sage") #functions in the context of the example


def MEUeq (h,b,Mtype):					#working example: MEUeq ([1,0,1],1/10,'all')  
   
   #Mtype gives the class of models under consideration
   if Mtype == 'cut':
      M = genMcut(h)
   if Mtype == 'all':
      M = genMall(h)
   if Mtype == 'cutnonempty':
      M = genMcutnonempty(h)
   if Mtype == 'allnonempty':
      M = genMallnonempty(h)
   if Mtype not in ['cut', 'all', 'cutnonempty', 'allnonempty']:
      raise Exception('Type of models unspecified!')
   
   #checks
   checkall(h,b,M)
   
   #create list of all sender strategies that should be considered according to the reduction lemma
   rM = reducemodels(M,h)
   N = len(rM)
   Pindlis = monotonepartition(list(range(N)))		#creates all monotonepartitons as a partition of indices over the set of reduced models rM
   
   #search for equilibria
   eqlis = []
   for Pind in Pindlis:
      P =[] 						#translate back to partition of models
      for pind in Pind:					#take a partition element of a partition Pind (indexes)
         P.append(flatten([rM[i] for i in pind]))	#create list of models according to pind and add them to the partition of models P

      oa = optimalmaxminaction(h,P)
      if senderoptimal(h,P,oa,b):
         eqlis.append((P,oa))
   
   return(eqlis)
   #return(cleanmultiple(eqlis))
   
def MLEUeq1 (h,b,Mtype):				#lists all MLEU equilibria by breaking ties in favor of the bias direction; working example: MLEUeq ([1,0,1],1/10,'all')
   
   #Mtype gives the class of models under consideration
   if Mtype == 'cut':
      M = genMcut(h)
   if Mtype == 'all':
      M = genMall(h)
   if Mtype == 'cutnonempty':
      M = genMcutnonempty(h)
   if Mtype == 'allnonempty':
      M = genMallnonempty(h)
   if Mtype not in ['cut', 'all', 'cutnonempty', 'allnonempty']:
      raise Exception('Type of models unspecified!')
   
   #checks
   checkall(h,b,M)
   
   #create list of all sender strategies that should be considered according to the reduction lemma
   rM = reducemodels(M,h)
   N = len(rM)
   Pindlis = monotonepartition(list(range(N)))		#creates all monotonepartitons as a partition of indices over the set of reduced models rM
   
   #search for equilibria
   eqlis = []
   for Pind in Pindlis:
      P =[] 						#translate back to partition of models
      for pind in Pind:					#take a partition element of a partition Pind (indexes)
         P.append(flatten([rM[i] for i in pind]))	#create list of models according to pind and add them to the partition of models P

      oa = optimallikeliaction(h,P)
      if senderoptimal(h,P,oa,b):
         eqlis.append((P,oa))
   
   return(eqlis)
   #return(cleanmultiple(eqlis))

def MLEUeqall (h,b,Mtype):				#lists all MLEU equilibria *for every consistent choice function* 
   
   #Mtype gives the class of models under consideration
   if Mtype == 'cut':
      M = genMcut(h)
   if Mtype == 'all':
      M = genMall(h)
   if Mtype == 'cutnonempty':
      M = genMcutnonempty(h)
   if Mtype == 'allnonempty':
      M = genMallnonempty(h)
   if Mtype not in ['cut', 'all', 'cutnonempty', 'allnonempty']:
      raise Exception('Type of models unspecified!')
   
   #checks
   checkall(h,b,M)
   
   #create list of all sender strategies that should be considered according to the reduction lemma
   rM = reducemodels(M,h)
   N = len(rM)
   
   #define choice function
   lchoice = list(listchoicefunctions (M,h))
   #print('lchoice is '+str(list(lchoice))+'\n')
   
   EQlis = []
   
   for cml in lchoice:
      Pindlis = monotonepartition(list(range(N)))#remove list() if not multiple choice functions are considered... #creates all monotonepartitons as a partition of indices over the set of reduced models rM
      #search for equilibria
      #print('Printing equilibria under the choice function '+str(cml)+':')
      eqlis = []
      for Pind in Pindlis:
         P =[] 							#translate back to partition of models
         for pind in Pind:					#take a partition element of a partition Pind (indexes)
       	    P.append(flatten([rM[i] for i in pind]))		#create list of models according to pind and add them to the partition of models P
         oa = optimallikeliactionchoice(h,P,cml)
         if senderoptimal(h,P,oa,b):
       	    eqlis.append((P,oa))
      if len(eqlis)>0:
         EQlis.append(('choice function: '+str(cml), eqlis))
   return(EQlis)
   #return(cleanmultiple(eqlis))
   
###
#N-Stage checker
###

def Nstagetester(hlen, bnum , bmax, Mtype,eqtypekey):
   #hlen = length of histories to check
   #bnum = number of biases to check
   #bmax = maximum bias (minimum is 0)
   #Mtype= class of models
   #eqtypekey = 'MEU', 'MLEU'
   
   blis = [i * bmax/(bnum + 1) for i in range(bnum + 1)]
   
   if Mtype == 'all':
      hlis = []
      constructer = genMall
      for n in range(hlen+1):
         hel = []
         while len(hel)<n:
            hel.append(1)
         while len(hel)<hlen:
            hel.append(0)
         hlis.append(hel)

         
   if Mtype == 'cut':
      raise Exception('Cut not fully implemented yet for the histories. Should write it with while-loops..')
      hlis = []
      constructer = genMcut
      for n in range(hlen+1):
         hel = []
         for i in range(n):
            hel.append(1)
         for j in range(hlen-i):
            hel.append(0)
         hlis.append(hel)
   
   if Mtype not in ['all','cut']:
      raise Exception('No valid model type given (expected all/cut).')
   
   
   if eqtypekey == 'MEU':
      eqtype = suffMEUeq
   if eqtypekey == 'MLEU':
      eqtype = suffMLEUeq
   if not eqtypekey in ['MEU','MLEU']:
      raise Exception('No valid equilibrium type given (expected: MEU, MLEU).')
   
   for h in hlis:
      M = constructer(h)
      for b in blis:
         eq = eqtype(h,b,Mtype)
         if not Nstagecheck(eq):
            print('The following equilibrium given b='+str(b)+' and h='+str(h)+' does not have the N-stage property:')
            return(eq)
         
   return('Everything looks good.')




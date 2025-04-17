
def bipart (X):
   #assuming X is an ordered list   
   ret =[]
   for i in range(len(X)-1):
      ret.append([X[:i+1],X[i+1:]])
   return(ret)
   


def bMEUmax (M, h):
   mlissorted = sorted(M,key = lambda m: quickmean(m,h))
   
   bstart = 0
   
   ##create bipartitions
   bi = bipart(mlissorted)
   
   print(bi)
   
   for M1,M2 in bi:
      #ensure 'just' equilibrium by comparing to rightmost a(m,h) in left partition M1
      x = quickmean(M1[len(M1)-1],h)
      
      btest = 1/2 * (findmode(M2,h)[0]+findmode(M1,h)[0]) -x
      if btest > bstart:
         bstart = btest
         
   return(bstart)
   
def bMLEUmax (M, h, cml = None): #don't forget to include a choice function if one wants to
   mlissorted = sorted(M,key = lambda m: quickmean(m,h))
   
   if cml == None:
      lcf = listchoicefunctions(M,h)
      cml = next(lcf)
      
      if (0,0) in M:
         while not emptylikelilast(cml):
            cml = next(lcf)
         print('No choice function given, working with '+str(cml)+' in the following, i.e., the first that orders the empty message last within its likelihood.')
   
      if (0,0) not in M:
         print('No choice function given, working with '+str(cml)+' in the following.')
   
   bstart = -1000
   
   ##create bipartitions
   bi = bipart(mlissorted)
   
   
   for M1,M2 in bi:
      #ensure 'just' equilibrium by comparing to rightmost a(m,h) in left partitionM1
      x = quickmean(M1[len(M1)-1],h)     

      
      btest = 1/2 * (findlikelichoice(M2,h,cml)[0]+findlikelichoice(M1,h,cml)[0]) - x
      if btest > bstart:
         bstart = btest
         
   return(bstart)
   

def plotbMEUmaxall(K,Mtype):
   H = Hlis(K)
   pointlis=[]
   
   for h in H:
      if Mtype == 'all':
         M = genMall(h)
      if Mtype == 'nonempty':
         M = genMallnonempty(h)
      pointlis.append((sum(h), bMEUmax(M,h)))
   
   pointssorted = sorted(pointlis, key = lambda tup : tup[0])
   
   lineplot(pointssorted)
   
   return(pointssorted)

def plotbMLEUmaxall(K,Mtype,cml = None):
   H = Hlis(K)
   pointlis=[]
   
   for h in H:
      if Mtype == 'all':
         M = genMall(h)
      if Mtype == 'nonempty':
         M = genMallnonempty(h)
      pointlis.append((sum(h), bMLEUmax(M,h)))
   
   pointssorted = sorted(pointlis, key = lambda tup : tup[0])
   
   lineplot(pointssorted)
   
   return(pointssorted)

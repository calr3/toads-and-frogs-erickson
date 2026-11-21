import sys
sys.path.insert(0,'/home/charlie/calr3gh/toads-and-frogs-erickson/tools')
from bounds import *
import cgt_values as C
from fractions import Fraction
import itertools, math
bad=0;tot=0
for n in range(2,12):
  for f in range(n):
    for mask in range(1<<(n-1)):
      cells=[i for i in range(n) if i!=f]
      s=['.']*n; s[f]='F'
      for j,c in enumerate(cells):
        if mask>>j&1: s[c]='T'
      s=''.join(s); g=C.tf(s); tot+=1
      u=0
      while not C.le(g,C.num(Fraction(u))): u+=1
      l=-1
      while C.le(C.num(Fraction(l+1)),g): l+=1
      if (u,l)!=(U(s),Lw(s)):
        bad+=1
        if bad<10: print(s,C.show(g),u,l,U(s),Lw(s))
print(tot,bad)

"""New proof generator, importing no object code. Signed integers are free generators."""
if not __debug__:
    raise SystemExit("Verification requires assertions; run without -O/-OO or PYTHONOPTIMIZE.")
import gzip,json,random,sys,time
from pathlib import Path
A,B,T,U,S,V=range(1,7)
def inverse(w): return [-x for x in w[::-1]]
def reduce(w):
    s=[]
    for x in w:
        if s and s[-1]==-x: s.pop()
        else: s.append(x)
    return s
def block(L,g=T):
    z=[]; p=0
    for q,c in L: z.extend([g]*(q-p)); z.append(c); p=q
    return z+[-g]*p
class Derivation:
    def __init__(self,w): self.initial=list(w); self.w=list(w); self.events=[]
    def move(self,p,n,new,free=False):
        old=self.w[p:p+n]; new=list(new)
        if old==new:return
        if free: assert reduce(old)==reduce(new)
        self.events.append((p,old,new,int(free))); self.w[p:p+n]=new
    def freely_reduce(self): self.move(0,len(self.w),reduce(self.w),True)
    def insert(self,other,p,mirror=False):
        size=len(other.initial)
        assert self.w[p:p+size]==(inverse(other.initial) if mirror else other.initial)
        for off,old,new,free in other.events:
            at=size-off-len(old) if mirror else off
            self.move(p+at,len(old),inverse(new) if mirror else new,free)
            size+=len(new)-len(old)
        assert self.w[p:p+size]==(inverse(other.w) if mirror else other.w)
def partition(L):
    d=Derivation(block(L)); I=max(q for q,c in L)//2
    atoms=[]
    for i in range(I+1):
        for q,c in L:
            if q//2==i: atoms.append(('O',[T,c,-T]) if q%2 else ('E',[c]))
        if i<I: atoms.append(('pair',[T,T]))
    atoms.extend([('pair',[-T,-T]) for _ in range(I)])
    d.move(0,len(d.w),[x for _,w in atoms for x in w],True)
    expanded=[]; pos=0
    for cat,w in atoms:
        if cat=='pair':
            new=[S,V] if w[0]>0 else [-V,-S]
            d.move(pos,2,new)
            expanded.extend([('E' if abs(x)==S else 'O',[x]) for x in new]); pos+=2
        else: expanded.append((cat,w)); pos+=len(w)
    # Bubble insertion in a token alphabet; tokens retain unreduced free words.
    atoms=expanded
    for i in range(len(atoms)):
        if atoms[i][0]!='E':continue
        j=i; pos=sum(len(w) for _,w in atoms[:j])
        while j and atoms[j-1][0]=='O':
            left,right=atoms[j-1][1],atoms[j][1]; pos-=len(left)
            d.move(pos,len(left)+len(right),right+left)
            atoms[j-1],atoms[j]=atoms[j],atoms[j-1]; j-=1
    even=[w for cat,w in atoms if cat=='E']; odd=[w for cat,w in atoms if cat=='O']
    return d,even,odd
def halve(L):
    d=Derivation(reduce(block(L,S)))
    p=0
    while p<len(d.w):
        x=d.w[p]
        if abs(x)==S: d.move(p,1,[U,T if x>0 else -T,-U]); p+=3
        else:p+=1
    d.freely_reduce()
    while True:
        hits=[i for i in range(len(d.w)-1) if d.w[i]==-U and abs(d.w[i+1]) in (A,B)]
        if not hits:break
        p=hits[0]; d.move(p,2,[d.w[p+1],-U]); d.freely_reduce()
    assert d.w==[U]+block(L)+[-U]
    return d
def fill(x,L):
    P=block(L); d=Derivation([x]+P+[-x]+inverse(P))
    if not L: d.freely_reduce(); return d
    q,es,os=partition(L)
    d.insert(q,1); d.insert(q,len(q.w)+2,True)
    E=[z for w in es for z in w]; O=[z for w in os for z in w]
    at=1+len(E)+len(O)
    for w in os[::-1]:
        at-=len(w); d.move(at,len(w)+1,[-x]+w)
    d.freely_reduce()
    ev=[(q//2,c) for q,c in L if q%2==0]
    if not ev:assert not d.w;return d
    # Keep the x and x^-1 ends even if an interior block freely collapses.
    Ered=reduce(E)
    d.move(0,len(d.w),[x]+Ered+[-x]+inverse(Ered),True)
    h=halve(ev); d.insert(h,1); d.insert(h,len(h.w)+2,True)
    Pp=block(ev)
    d.move(0,2,[U,x])
    at=2+len(Pp); d.move(at,2,[-x,-U]); d.freely_reduce()
    sub=fill(x,ev)
    d.move(0,len(d.w),[U]+sub.initial+[-U],True)
    d.insert(sub,1);d.freely_reduce();assert not d.w
    return d
def main():
    out=Path(__file__).parent
    rng=random.Random(8675309)
    cases=[]
    for K in [16,64,128]:
        L=[(q,c) for q in range(1,K+1) for c in ([A,B,A] if q%2 else [B,A,B])]
        cases.append(('full3_'+str(K),A,L))
    L=[(q,rng.choice([A,B])) for q in range(1,48) for _ in range(rng.randrange(4))]
    cases.append(('random_47',B,L))
    for n in range(3):
        L=[(q,c) for q in range(1,129) for c in rng.choice([[A,B,A],[B,A,B]])]
        cases.append(('random_full3_128_'+str(n),rng.choice([A,B]),L))
    for name,x,L in cases:
        start=time.monotonic();d=fill(x,L)
        path=out/(name+'.certificate.jsonl.gz')
        with gzip.open(path,'wt',encoding='utf8',compresslevel=1) as f:
            f.write(json.dumps({'initial':d.initial,'lamps':L,'x':x})+'\n')
            for e in d.events:f.write(json.dumps(e,separators=(',',':'))+'\n')
        cells=sum(not e[3] for e in d.events);K=max(q for q,c in L)
        print(json.dumps({'case':name,'K':K,'letters':len(L),'cells':cells,'ratio_exact':str(cells)+'/'+str(K*K),'events':len(d.events),'seconds':round(time.monotonic()-start,3)}),flush=True)
if __name__=='__main__':main()

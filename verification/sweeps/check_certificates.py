"""Standalone checker: no imports from either source object or our generator.
Reconstruct each cell conjugate, multiply all conjugates, freely reduce, compare boundary.
"""
if not __debug__:
    raise SystemExit("Verification requires assertions; run without -O/-OO or PYTHONOPTIMIZE.")
import gzip,json,sys,time
from pathlib import Path
def inv(w):return [-a for a in reversed(w)]
def append_reduce(s,w):
    for a in w:
        if s and s[-1]==-a:s.pop()
        else:s.append(a)
def red(w):
    s=[];append_reduce(s,w);return s
def comm(x,y):return x+y+inv(x)+inv(y)
rels=[[1,1],[2,2],[1,2]*3,[-5,4,3,-4],[-6,3,5,-3],[3,3,-6,-5],comm([5],[6])]
for x in [1,2]:
    rels.extend([comm([4],[x]),comm([6],[x]),comm([5],[3,x,-3])])
    for y in [1,2]:rels.append(comm([x],[3,y,-3]))
assert len(rels)==17
allowed={}
for idx,r in enumerate(rels):
    for sign,z in [(1,r),(-1,inv(r))]:
        for i in range(len(z)):allowed[tuple(z[i:]+z[:i])]=(idx,sign)
for path in sorted(Path(__file__).parent.glob('*.certificate.jsonl.gz')):
    start=time.monotonic();prod=[];counts={};cells=0;events=0;maxstack=0
    with gzip.open(path,'rt',encoding='utf8') as f:
        header=json.loads(next(f));initial=header['initial'];current=initial.copy()
        wanted=[];position=0
        for q,c in header['lamps']:
            assert q>=position and c in [1,2]
            wanted += [3]*(q-position)+[c];position=q
        wanted += [-3]*position
        assert initial==[header['x']]+wanted+[-header['x']]+inv(wanted)
        for line in f:
            at,old,new,free=json.loads(line);events+=1
            assert current[at:at+len(old)]==old,(path,events,'old mismatch')
            if free:assert red(old)==red(new)
            else:
                z=red(old+inv(new));head=[]
                while len(z)>1 and z[0]==-z[-1]:head.append(z[0]);z=z[1:-1]
                assert tuple(z) in allowed,(path,events,z)
                idx,sign=allowed[tuple(z)];counts[idx]=counts.get(idx,0)+1
                # q r q^-1, with r a signed cyclic rotation of a defining relator.
                q=current[:at]+head
                append_reduce(prod,q);append_reduce(prod,z);append_reduce(prod,inv(q));cells+=1
                maxstack=max(maxstack,len(prod))
            current[at:at+len(old)]=new
    assert red(current)==[]
    assert prod==red(initial),(path,'product boundary mismatch')
    K=max(q for q,c in header['lamps'])
    print(json.dumps({'certificate':path.name,'cells':cells,'K':K,'ratio_exact':str(cells)+'/'+str(K*K),'free_product_equals_boundary':True,'final_word_empty':True,'max_product_stack':maxstack,'relator_counts':counts,'seconds':round(time.monotonic()-start,3)}),flush=True)


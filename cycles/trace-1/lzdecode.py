# Decode a live.lean-lang.org `#codez=` link to the Lean text it carries (cycle 1 of DEBRIEF-math-erdos671).
# The fragment is lz-string compressToBase64 output, percent-encoded. This is a minimal re-implementation of
# lz-string's decompressFromBase64 (and the URI-safe alphabet), decoding as far as the stream allows and reporting
# whether the end-of-stream marker was reached (a truncated link stops early).
# usage: python3 -I lzdecode.py URLFILE > decoded.lean     (URLFILE holds the full link on one line)
import sys, urllib.parse
B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/="
URI = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+-$"
def decompress(s, alpha, reset=32):
    vals=[alpha.index(c) for c in s]
    pos=[0]; data={'val':vals[0],'position':reset,'index':1}
    def bits(n):
        r=0; p=1
        for _ in range(n):
            resb=data['val'] & data['position']
            data['position']>>=1
            if data['position']==0:
                data['position']=reset
                if data['index']>=len(vals): raise EOFError
                data['val']=vals[data['index']]; data['index']+=1
            r|= p if resb>0 else 0; p<<=1
        return r
    d={0:0,1:1,2:2}; enlargeIn=4; dictSize=4; numBits=3; out=[]
    nxt=bits(2)
    if nxt==2: return ""
    c=chr(bits(8 if nxt==0 else 16)); d[3]=c; w=c; out.append(c)
    try:
        while True:
            c=bits(numBits)
            if c in (0,1):
                d[dictSize]=chr(bits(8 if c==0 else 16)); c=dictSize; dictSize+=1; enlargeIn-=1
            elif c==2: return "".join(out), True
            if enlargeIn==0: enlargeIn=2**numBits; numBits+=1
            if c in d: entry=d[c]
            elif c==dictSize: entry=w+w[0]
            else: return "".join(out), False
            out.append(entry); d[dictSize]=w+entry[0]; dictSize+=1; enlargeIn-=1; w=entry
            if enlargeIn==0: enlargeIn=2**numBits; numBits+=1
    except EOFError:
        return "".join(out), False
url=open(sys.argv[1]).read().strip()
frag=url.split('#codez=',1)[1]
s=urllib.parse.unquote(frag)
alpha = B64 if ('/' in s or '=' in s) else URI
txt,complete=decompress(s,alpha)
sys.stderr.write(f"alphabet={'base64' if alpha==B64 else 'uri'} decoded_chars={len(txt)} terminated_by_end_marker={complete}\n")
sys.stdout.write(txt.encode("utf-16","surrogatepass").decode("utf-16"))

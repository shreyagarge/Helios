import hashlib

p = 19557005198709002903944860293031210393112763219086296641657077101075696217230957575932867920574816565856404011416908876733063974554042055901449481509845537165833627083609136426386625960849573203936690977282752217830467255076903813033768202255463477317279507253420233052258146393806024179130344501759742626253484354878829682461413002143954786668386100202257237258007726886368228024987052808444032800050116408995869561195208576647050961019393809940446490709061546503439488751331252440431940049716566765873615456614911458658341732120931319694200689362617296630728389003180670326151653001322354906363854478585334821235883

q = Integer((p-1)/2)

m=0
g1 = 4;
g2 = power_mod(g1,12,p)
x = ZZ.random_element(q);
R = power_mod(g1,x,p);
S = power_mod(g2,x,p) * g1^m;

#setup complete
#disjprove and disjverify

def DisjProve(g,h,R,S,x,m):
    if(m==1):
        ch0 = ZZ.random_element(q);
        rep0 = ZZ.random_element(q);
        U0 = Mod(power_mod(g,rep0,p)/power_mod(R,ch0,p), p);
        V0 = Mod(power_mod(h,rep0,p)/power_mod(S,ch0,p), p);

        u1 = ZZ.random_element(q);
        U1 = power_mod(g,u1,p);
        V1 = power_mod(h,u1,p);

        hash_value = hashlib.sha256(str(R) + str(S) + str(U0) + str(V0) + str(U1) + str(V1)).hexdigest();
        ch = Integer(int(hash_value,16),q);
        ch1= Integer(Mod(ch-ch0,q));
        rep1 = Integer(Mod(u1+ch1*x, q));
    elif(m==0):
        u0 = ZZ.random_element(q);
        U0 = power_mod(g,u0,p);
        V0 = power_mod(h,u0,p);

        ch1 = ZZ.random_element(q);
        rep1 = ZZ.random_element(q);
        U1 = Mod(power_mod(g,rep1,p)/power_mod(R,ch1,p), p);
        V1 = Mod(power_mod(h,rep1,p)/power_mod(S*power_mod(g,-1,p),ch1,p), p);

        hash_value = hashlib.sha256(str(R) + str(S) + str(U0) + str(V0) + str(U1) + str(V1)).hexdigest();
        ch = Integer(int(hash_value,16),q);
        ch0 = Integer(Mod(ch-ch1,q));
        rep0 = Integer(Mod(u0+ch0*x,q));
    return [ch0,ch1,rep0,rep1]

def DisjVerify(g,h,R,S,ch0,ch1,rep0,rep1):
    lhs=Mod(ch0+ch1,q);
    t1=Mod(power_mod(g,rep0,p)/power_mod(R,ch0,p), p);
    t2=Mod(power_mod(h,rep0,p)/power_mod(S,ch0,p), p);
    t3=Mod(power_mod(g,rep1,p)/power_mod(R,ch1,p), p);
    t4=Mod(power_mod(h,rep1,p)/power_mod(S*power_mod(g,-1,p),ch1,p), p);
    hash_value = hashlib.sha256(str(R) + str(S) + str(t1) + str(t2) + str(t3) + str(t4)).hexdigest();
    rhs = Mod(int(hash_value,16),q);
    if(rhs==lhs):
        return "accept"
    else:
        return "reject"

#test

[ch0,ch1,rep0,rep1] = DisjProve(g1,g2,R,S,x,m);
decision = DisjVerify(g1,g2,R,S,ch0,ch1,rep0,rep1);
print decision

#helios setup

def PrEq(pk,y1,y2,sk):
    r = ZZ.random_element(q);
    com1 = power_mod(g1,r,p);
    com2 = power_mod(pk,r,p);
    hash_value = hashlib.sha256(str(y1) + str(y2) + str(com1) + str(com2)).hexdigest();
    ch = Integer(int(hash_value,16),q);
    s = Integer(Mod(r + sk * ch,q));
    return [ch,s]

def VerifyEq(pk,y1,y2,ch,s):
    com1 = Mod(power_mod(g1,s,p) * inverse_mod(power_mod(y1,ch,p),p),p);
    com2 = Mod(power_mod(g2,s,p) * inverse_mod(power_mod(y2,ch,p),p),p);
    hash_value = hashlib.sha256(str(y1) + str(y2) + str(com1) + str(com2)).hexdigest();
    return ch == Integer(int(hash_value,16),q)

# key generation
def Setup():
    sk = ZZ.random_element(q);
    pk = power_mod(g1,sk,p);
    return [sk, pk]

# Modified ElGamal Encryption of vote 'v'.
def Vote(pk, v):
    x = ZZ.random_element(q);
    R = power_mod(g1,x,p);
    S = power_mod(pk,x,p) * g1^v;
    return [R,S, DisjProve(g1, pk, R, S, x, v)]
# Homomorphic property of ElGamal used to tally votes without decrypting them.
def Tally(BB, pk, sk):
    result = 0
    Rsum = None
    Ssum = None
    for b in BB:
        if DisjVerify(g1, pk, b[0], b[1], b[2][0], b[2][1], b[2][2], b[2][3]) == "reject":
            return ["invalid", None];
        if Rsum == None:
            Rsum = b[0];
            Ssum = b[1];
            continue;

        Rsum = Integer(Mod(Rsum*b[0],p));   # Rsum=g1^(sum of all x's)
        Ssum = Integer(Mod(Ssum*b[1],p));   # Ssum=pk^(sum of all x's).g1^(sum of all votes)

    gres = Integer(Mod(Ssum*power_mod(power_mod(Rsum,sk,p),-1,p),p));  #multiplying Rsum and Ssum gives g1^(sum of all votes)
    pi = PrEq(pk, Rsum, Mod(Ssum*power_mod(gres,-1,p), p), sk);        
    #proof of result using EqDl proof System


    return [log(gres,g1), pi]               
    # return the result and proof of correctness


    #test helios

YesVotes = 5 #input to test
BB = [] ;
[sk,pk] = Setup();

#constructing a ballot 5 yes and 10 no votes, and each vote is encrypted using the public key.
for i in xrange(1,15):
    if YesVotes > 0:
        YesVotes -= 1;
        BB.append(Vote(pk, 1));
    else:
        BB.append(Vote(pk, 0));


[result,proof] = Tally(BB, pk, sk)
print "Result: ",result

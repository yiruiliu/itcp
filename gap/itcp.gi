################################################################################
##
##                                                                 itcp package
##
##  Copyright 2016,                                                Jayant Apte
##                                                                 John Walsh
##
##  The .gi file containing implementation part of the itcp package.
##
################################################################################

# Utility functions

if not IsBound(DeepCopy_lol) then
DeepCopy_lol:=function(lol)
  local olol,l;
  olol:=[];
  for l in lol do
  Append(olol,[ShallowCopy(l)]);
  od;
  return olol;
end;
fi;

if not IsBound(RecNamesInt) then
RecNamesInt:=function(r)
  # Returns all values in a record
  local i,intnames;
  intnames:=[];
  for i in RecNames(r) do
   Append(intnames,[Int(i)]);
  od;
  return intnames;
end;
fi;

if not IsBound(skipline) then
skipline:=function(str,i)
local j;
if i>Size(str) or i<0 then
  return -1;
fi;
for j in [i..Size(str)] do
  if str[j]='\n' then
    if j=Size(str) then
      return -1;
    else
      return j+1;
    fi;
  fi;
od;
return -1;
end;
fi;


if not IsBound(set2int) then
set2int:=function(s)
  local i,j;
  i:=0;
  for j in s do
    i:=i+2^(Int(j)-1);
  od;
  return i;
end;
fi;

if not IsBound(GenShannonBounded) then
GenShannonBounded:=function(n)
local rlist,mtx,str,i,j,shineq,nset_i,ineq,pairs,p,Klist,K,nset_ij,greq,neq,A,b,sum2one,s;
shineq:=[];
# first add H(X_i|rest)>=0 type inequalities
for i in [1..n] do
  nset_i:=[1..n];
  SubtractSet(nset_i,[i]);
  ineq:=ZeroMutable([1..2^n]);
  ineq[set2int([1..n])+1]:=1;
  ineq[set2int(nset_i)+1]:=-1;
  Append(shineq,[ineq]);
od;
# second, add I(X_i,X_j|X_K) >=0
pairs:=Combinations([1..n],2);
for p in pairs do
  nset_ij:=[1..n];
  SubtractSet(nset_ij,p);
  Klist:=Combinations(nset_ij);
  for K in Klist do
    ineq:=ZeroMutable([1..2^n]);
    ineq[set2int(Union(K,[p[1]]))+1]:=1;
    ineq[set2int(Union(K,[p[2]]))+1]:=1;
    ineq[set2int(Union(K,p))+1]:=-1;
    if Size(K)>0 then
      ineq[set2int(K)+1]:=-1;
    fi;
    Append(shineq,[ineq]);
  od;
od;
shineq:=-shineq;
sum2one:=ZeroMutable([1..2^n-1]);
for i in [1..2^n-1] do
sum2one[i]:=1;
od;
A:=[];
b:=[];
for s in shineq do
  Append(A,[s{[2..Size(s)]}]);
  Append(b,[0]);
od;
Append(A,[sum2one]);
Append(b,[1]);
return [A,b];
end;
fi;

if not IsBound(GenShannonUnBounded) then
GenShannonUnBounded:=function(n)
# returns [A,b] s.t. Ax<=b are the inequalities
local rlist,mtx,str,i,j,shineq,nset_i,ineq,pairs,p,Klist,K,nset_ij,greq,neq,A,b,sum2one,s;
shineq:=[];
# first add H(X_i|rest)>=0 type inequalities
for i in [1..n] do
  nset_i:=[1..n];
  SubtractSet(nset_i,[i]);
  ineq:=ZeroMutable([1..2^n]);
  ineq[set2int([1..n])+1]:=1;
  ineq[set2int(nset_i)+1]:=-1;
  Append(shineq,[ineq]);
od;
# second, add I(X_i,X_j|X_K) >=0
pairs:=Combinations([1..n],2);
for p in pairs do
  nset_ij:=[1..n];
  SubtractSet(nset_ij,p);
  Klist:=Combinations(nset_ij);
  for K in Klist do
    ineq:=ZeroMutable([1..2^n]);
    ineq[set2int(Union(K,[p[1]]))+1]:=1;
    ineq[set2int(Union(K,[p[2]]))+1]:=1;
    ineq[set2int(Union(K,p))+1]:=-1;
    if Size(K)>0 then
      ineq[set2int(K)+1]:=-1;
    fi;
    Append(shineq,[ineq]);
  od;
od;
shineq:=-shineq;
sum2one:=ZeroMutable([1..2^n-1]);
for i in [1..2^n-1] do
sum2one[i]:=1;
od;
A:=[];
b:=[];
for s in shineq do
  Append(A,[s{[2..Size(s)]}]);
  Append(b,[0]);
od;
#Append(A,[sum2one]);
#Append(b,[1]);
return [A,b];
end;
fi;

if not IsBound(DeepSort) then
DeepSort:=function(list,nlevels,l)
  local soretdlist,i;
  # l is current level
  # level:=1: only ``list`` is sorted at top level
  # level:=2: each element of list is also sorted and so on...
  # levels 1 and nlevels won't be sorted
  if nlevels = 1 then
    return list;
  fi;
  if nlevels=l then
    return list;
  else
    soretdlist:=EmptyPlist(Size(list));
    for i in [1..Size(list)] do
      soretdlist[i]:=DeepSort(list[i],nlevels,l+1);
      od;
    return soretdlist;
  fi;
end;
fi;

if not IsBound(nextnum) then
nextnum:=function(str,i)
local foundnum, j,k,isneg;
if i>Size(str) or i<0 then
  return -1;
fi;
foundnum:=false;
isneg:=false;
for j in [i..Size(str)] do
  if not str[j]=' ' then
    if IsDigitChar(str[j]) then
      if j-1>=1 and str[j-1]='-' then
        isneg:=true;
      fi;
      foundnum:=true;
      break;
    fi;
  fi;
od;
if foundnum=false then
 return [false,-1,-1]; # [found?, number, next_i]
fi;
for k in [j+1..Size(str)] do
  if not IsDigitChar(str[k]) then
    break;
  fi;
od;
if isneg=true then
  return [true,Int(str{[j-1..k-1]}),k];
else
  return [true,Int(str{[j..k-1]}),k];
fi;
end;
fi;

if not IsBound(writeinefile) then
writeinefile:=function(fname,lin,mtx)
#  mtx is the matrix [b A] s.t. b+Ax>=0 is the H-representation
local ostr,row,i,r;
ostr:="";
if Size(lin)=0 then
  ostr:=Concatenation(ostr,"H-representation\nbegin\n",String(Size(mtx))," ",String(Size(mtx[1])), " rational\n");
else
  ostr:= Concatenation(ostr,"H-representation\n","linearity ",String(Size(lin))," ");
  for r in lin do
      ostr:=Concatenation(ostr,String(r)," ");
  od;
  ostr:=Concatenation(ostr,"\nbegin\n",String(Size(mtx))," ",String(Size(mtx[1])), " rational\n");
fi;
for i in [1..Size(mtx)] do
    row:=mtx[i];
    #ostr:=Concatenation(ostr,"0 ");
    for r in row do
        ostr:=Concatenation(ostr,String(r)," ");
    od;
    ostr:=Concatenation(ostr,"\n");
od;
ostr:=Concatenation(ostr,"end");
PrintTo(fname,ostr);
end;
fi;

if not IsBound(writeinefile_cone) then
writeinefile_cone:=function(fname,lin,mtx1)
# mtx1 is the matrix A s.t. Ax<=0 is the cone
local ostr,row,i,r,mtx;
mtx:=[];
for i in [1..Size(mtx1)] do
  row:=[0];
  Append(row,-mtx1[i]);
  Append(mtx,[row]);
od;
ostr:="";
if Size(lin)=0 then
  ostr:=Concatenation(ostr,"H-representation\nbegin\n",String(Size(mtx))," ",String(Size(mtx[1])), " rational\n");
else
  ostr:= Concatenation(ostr,"H-representation\n","linearity ",String(Size(lin))," ");
  for r in lin do
      ostr:=Concatenation(ostr,String(r)," ");
  od;
  ostr:=Concatenation(ostr,"\nbegin\n",String(Size(mtx))," ",String(Size(mtx[1])), " rational\n");
fi;
for i in [1..Size(mtx)] do
    row:=mtx[i];
    #ostr:=Concatenation(ostr,"0 ");
    for r in row do
        ostr:=Concatenation(ostr,String(r)," ");
    od;
    ostr:=Concatenation(ostr,"\n");
od;
ostr:=Concatenation(ostr,"end");
PrintTo(fname,ostr);
end;
fi;

if not IsBound(writeextfile_cone) then
writeextfile:=function(fname,raylist)
  local ostr,row,i,r;
  ostr:="";
  ostr:=Concatenation(ostr,"V-representation\nbegin\n",String(Size(raylist))," ",String(Size(raylist[1])+1), " rational\n");
  for i in [1..Size(raylist)] do
      row:=[0];
      Append(row,raylist[i]);
      #ostr:=Concatenation(ostr,"0 ");
      for r in row do
          ostr:=Concatenation(ostr,String(r)," ");
      od;
      ostr:=Concatenation(ostr,"\n");
  od;
  ostr:=Concatenation(ostr,"end");
  PrintTo(fname,ostr);
  end;
fi;

# ITCP functions
InstallGlobalFunction(NetSymGroup,
function(NC)
local N,Nx,c,G1,G;
# clean NC
N:=NC[1];
Nx:=SortedCons(N);
# compute stab
G1:=Stabilizer(SymmetricGroup(NC[3]),Nx,OnNCinstance);
G:=Stabilizer(G1,[1..NC[2]],OnSets);
return G;
end);


SSSymGroup:=function(Asets,nvars)
local G1,G,s,AsetsClean;
G:=Stabilizer(SymmetricGroup(nvars),1);
# clean Asets
AsetsClean:=[];
for s in Asets do
  Append(AsetsClean,[AsSet(s)]);
od;
AsetsClean:=AsSet(AsetsClean);
# compute stabgroup of Asets
G1:=Stabilizer(G,AsetsClean,OnSetsSets);
return G1;
end;

GGSymGroup:=function(G)
  local lot,v,i,G1;
  lot:=[];
  for v in RecNamesInt(G[2]) do
    for i in G[2].(v) do
      Append(lot,[[i,v]]);
    od;
  od;
  lot:=AsSet(lot);
  G1:=SymmetricGroup(Size(G[1]));
  return Stabilizer(G1,lot,OnSetsTuples);
end;

NCShannonBounded:=function(ncinstance)
local ShOB,i,linrows,con,conlin,j,conineq;
  ShOB:=GenShannonUnBounded(ncinstance[3]);
  i:=Size(ShOB[1])+1;
  linrows:=[];
  # node constraints
  for con in ncinstance[1] do
    conlin:=ZeroMutable([1..2^ncinstance[3]-1]);
    conlin[set2int(con[1])]:=1;
    conlin[set2int(con[2])]:=-1;
    Append(ShOB[1],[conlin]);
    Append(ShOB[2],[0]);
    Append(linrows,[i]);
    i:=i+1;
  od;
  # source independence
  conlin:= ZeroMutable([1..2^ncinstance[3]-1]);
  for j in [1..ncinstance[2]] do
  conlin[set2int([j])]:=1;
  od;
  conlin[set2int([1..ncinstance[2]])]:=-1;
  Append(ShOB[1],[conlin]);
  Append(ShOB[2],[0]);
  Append(linrows,[i]);
  i:=i+1;
  # source and edge rates
  for j in [1..Size(ShOB[1])] do
  ShOB[1][j]:=Concatenation(ZeroMutable([1..ncinstance[3]]),ShOB[1][j]);
  od;
  for j in [1..ncinstance[2]] do # source rate ineq
    conineq:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
    conineq[j]:=1;
    conineq[ncinstance[3]+set2int([j])]:=-1;
    Append(ShOB[1],[conineq]);
    Append(ShOB[2],[0]);
    conineq:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
    conineq[j]:=-1; # non-negative
    Append(ShOB[1],[conineq]);
    Append(ShOB[2],[0]);
  od;
  for j in [ncinstance[2]+1..ncinstance[3]] do # edge rate ineq
    conineq:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
    conineq[j]:=-1;
    conineq[ncinstance[3]+set2int([j])]:=1;
    Append(ShOB[1],[conineq]);
    Append(ShOB[2],[0]);
    conineq:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
    conineq[j]:=-1; # non-negative
    Append(ShOB[1],[conineq]);
    Append(ShOB[2],[0]);
  od;
  # sum<=1 for rates
  conineq:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
  for j in [1..ncinstance[3]] do
    conineq[j]:=1;
  od;
  Append(ShOB[1],[conineq]);
  Append(ShOB[2],[1]);
  return [ShOB[1],ShOB[2],linrows];
end;

ProofParseShannon:=function(ncinstance,lvec)
  local ShOB,i,linrows,con,conlin,j,conineq,displaystr,nset_i,rowcnt,K,Klist,nset_ij,pairs,p;
    displaystr:="";
    ShOB:=GenShannonUnBounded(ncinstance[3]);
    for i in [1..ncinstance[3]] do
      if lvec[i]>0 then
        nset_i:=[1..ncinstance[3]];
        SubtractSet(nset_i,[i]);
        displaystr:=Concatenation(displaystr," ",String(lvec[i])," ","H(",String(i),"|",String(nset_i),")>=0 \n");
      fi;
    od;
    rowcnt:=ncinstance[3]+1;
    # second, add I(X_i,X_j|X_K) >=0
    pairs:=Combinations([1..ncinstance[3]],2);
    for p in pairs do
      nset_ij:=[1..ncinstance[3]];
      SubtractSet(nset_ij,p);
      Klist:=Combinations(nset_ij);
      for K in Klist do
        if lvec[rowcnt]>0 then
          if Size(K)>0 then
            displaystr:=Concatenation(displaystr," ",String(lvec[rowcnt])," ","I( ",String(p[1])," ; ",String(p[2]),"| ",String(K),")>=0 \n" );
          else
            displaystr:=Concatenation(displaystr," ",String(lvec[rowcnt])," ","I( ",String(p[1])," ; ",String(p[2]), ")" ,">=0 \n" );
          fi;
        fi;
        rowcnt:=rowcnt+1;
      od;
    od;
    Display(displaystr);
    linrows:=[];
    # node constraints
    for con in ncinstance[1] do
      if lvec[rowcnt]>0 then
        displaystr:=Concatenation(displaystr,String(lvec[rowcnt]), String(" -"),"H(",String(con[1]),") + H(",String(con[2]),")>=0 \n" );
      fi;
      rowcnt:=rowcnt+1;
    od;
    # source independence
    if lvec[rowcnt]>0 then
      displaystr:=Concatenation(displaystr,String(lvec[rowcnt]), " - sum_[",String(ncinstance[2]),"] H(i) + H(",String([1..ncinstance[2]]),")>=0 \n" );
    fi;
    rowcnt:=rowcnt+1;
    # source and edge rates
    for j in [1..ncinstance[2]] do # source rate ineq
      if lvec[rowcnt]>0 then
        displaystr:=Concatenation(displaystr,String(lvec[rowcnt])," - w_",String(j),"+ H(",String(j),")>=0 \n");
      fi;
      rowcnt:=rowcnt+1;
      if lvec[rowcnt]>0 then
        displaystr:=Concatenation(displaystr,String(lvec[rowcnt])," w_",String(j),">=0 \n");
      fi;
      rowcnt:=rowcnt+1;
    od;
    for j in [ncinstance[2]+1..ncinstance[3]] do # edge rate ineq
      if lvec[rowcnt]>0 then
        displaystr:=Concatenation(displaystr,String(lvec[rowcnt])," R_",String(j),"- H(",String(j),")>=0 \n");
      fi;
      rowcnt:=rowcnt+1;
      if lvec[rowcnt]>0 then
        displaystr:=Concatenation(displaystr,String(lvec[rowcnt])," R_",String(j),">=0");
      fi;
      rowcnt:=rowcnt+1;
    od;

    for con in ncinstance[1] do
      if lvec[rowcnt]>0 then
        displaystr:=Concatenation(displaystr,String(lvec[rowcnt])," H(",String(con[1]),") - H(",String(con[2]),")>=0 \n" );
      fi;
      rowcnt:=rowcnt+1;
    od;
    # source independence
    if lvec[rowcnt]>0 then
      displaystr:=Concatenation(displaystr,String(lvec[rowcnt]), " sum_[",String(ncinstance[2]),"] H(i) - H(",String([1..ncinstance[2]]),")>=0" );
    fi;
    rowcnt:=rowcnt+1;
    return displaystr;
end;

DualProofShannonL1:=function(ncinstance,ineq)
  # Construct Shannon cone, with network constraints
  local rlist,A,i,At,obj,b,onemap,rlist1,s,rlist2,linrows,nnineq,linrows1;
  rlist:=NCShannonBounded(ncinstance);
  # Get rid of the sum to one ineq
  A:=-rlist[1]{[1..Size(rlist[1])-1]};
  # Convert equalities to inequalities
  linrows:=rlist[3];
  Append(A,-A{linrows});
  At:=MutableMatrix(TransposedMat(A));
  linrows1:=[1..Size(At)];
  for i in [1..Size(At[1])] do
    nnineq:=ZeroMutable([1..Size(At[1])]);
    nnineq[i]:=-1;
    Append(At,[nnineq]);
  od;
  onemap := function ( x ) return 1; end;
  obj:=-List([1..Size(At[1])],onemap);
  b:=Concatenation(-ineq,ZeroMutable([1..Size(At)-Size(ineq)]));
  rlist1:=LoadQSLP(obj,At,b,linrows1,qs_exec);
  s:=rlist1[1];
  SolveQSLP(s,[]);
  rlist2:=GetQSLPsol_primal(s);; # get primal solution
  Display(rlist2[5]);
  CloseStream(s);
end;

NCShannonCaps:=function(ncinstance,caps)
# Shannon + network constraints + capacity caps on edge rates
local ShOB,i,linrows,con,conlin,j,conineq;
  ShOB:=GenShannonUnBounded(ncinstance[3]);
  # make all source entropies same
  i:=Size(ShOB[1])+1;
  linrows:=[];
  # node constraints
  for con in ncinstance[1] do
    conlin:=ZeroMutable([1..2^ncinstance[3]-1]);
    conlin[set2int(con[1])]:=1;
    conlin[set2int(con[2])]:=-1;
    Append(ShOB[1],[conlin]);
    Append(ShOB[2],[0]);
    Append(linrows,[i]);
    i:=i+1;
  od;
  # source independence
  conlin:= ZeroMutable([1..2^ncinstance[3]-1]);
  for j in [1..ncinstance[2]] do
  conlin[set2int([j])]:=1;
  od;
  conlin[set2int([1..ncinstance[2]])]:=-1;
  Append(ShOB[1],[conlin]);
  Append(ShOB[2],[0]);
  Append(linrows,[i]);
  i:=i+1;
  # source and edge rates, here we substitute edge capacities
  for j in [1..Size(ShOB[1])] do
  ShOB[1][j]:=Concatenation(ZeroMutable([1..ncinstance[3]]),ShOB[1][j]);
  od;
  i:=Size(ShOB[1])+1;
  # if ncinstance[2]>1 then
  #   for j in [1..ncinstance[2]-1] do
  #     conlin:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
  #     conlin[j]:=1;
  #     conlin[j+1]:=-1;
  #     Append(ShOB[1],[conlin]);
  #     Append(ShOB[2],[0]);
  #     Append(linrows,[i]);
  #     i:=i+1;
  #   od;
  # fi;
  for j in [1..ncinstance[2]] do # source rate ineq
    conineq:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
    conineq[j]:=1;
    conineq[ncinstance[3]+set2int([j])]:=-1;
    Append(ShOB[1],[conineq]);
    Append(ShOB[2],[0]);
    conineq:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
    conineq[j]:=-1; # non-negative
    Append(ShOB[1],[conineq]);
    Append(ShOB[2],[0]);
  od;
  for j in [ncinstance[2]+1..ncinstance[3]] do # edge rate ineq + capacity ineq
    conineq:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
    conineq[j]:=-1;
    conineq[ncinstance[3]+set2int([j])]:=1;
    Append(ShOB[1],[conineq]);
    Append(ShOB[2],[0]);
    conineq:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
    conineq[j]:=-1; # non-negative
    Append(ShOB[1],[conineq]);
    Append(ShOB[2],[0]);
    conineq:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
    conineq[j]:=1; # capacity bound
    Append(ShOB[1],[conineq]);
    Append(ShOB[2],[caps[j-ncinstance[2]]]);
  od;
  return [ShOB[1],ShOB[2],linrows];
end;


# sed to filter copy strings etc from list in DFZ paper: $  cat dfznonshannon.txt | sed 's/^[^)]*)//g' |  sed 's/[a-z]*//g' | tr -d '.' | tr -d '(' | tr -d ')' | sed 's/\s*$//g' |  sed 's/^ /[/' | sed 's/$/],/' | sed 's/ /,/g' | tr '\n' ' ' > dfznonshannon_clean.txt

NonShannon4:= function()
return [[2,4,2,1,3,1,0,2,0], [2,3,3,1,5,2,0,2,0], [3,6,3,1,6,3,0,3,0], [2,4,2,1,2,0,0,2,3], [2,3,3,2,2,0,0,2,0], [4,6,4,3,4,2,1,4,0], [2,5,2,1,2,0,0,2,0], [2,4,3,1,2,0,0,2,0], [2,4,1,2,2,3,0,2,0], [3,7,4,1,4,1,0,3,0], [4,6,11,3,6,2,0,4,0], [3,6,3,1,4,1,0,3,5], [7,8,12,12,7,5,5,7,0], [5,14,9,1,7,2,0,5,0], [6,7,11,11,6,3,3,6,0], [3,4,6,3,6,2,0,3,0], [11,23,28,3,11,7,5,11,0], [5,6,8,7,5,3,2,5,0], [6,12,6,3,6,4,3,6,0], [4,5,16,4,10,6,0,4,0], [3,6,5,1,5,3,0,3,0], [4,13,7,1,4,2,2,4,0], [4,5,7,6,4,1,1,4,0], [4,8,4,1,10,6,0,4,0], [5,16,13,1,5,1,1,5,0], [5,6,11,11,5,1,1,5,0], [2,3,4,1,4,5,0,2,0], [4,5,6,4,4,2,4,4,0], [4,7,4,2,4,1,1,4,7], [2,3,3,1,2,3,2,2,0], [4,10,2,3,9,9,0,4,0], [4,7,3,4,5,5,0,4,0], [3,5,4,2,3,0,0,3,4], [5,14,11,1,5,2,2,5,0], [6,15,10,2,6,0,0,6,11], [11,31,18,3,13,4,0,11,0], [18,38,31,6,18,6,6,18,0], [4,9,3,2,8,4,0,4,0], [5,12,3,3,10,9,0,5,0], [8,19,6,4,9,14,0,8,0], [3,5,4,2,4,1,0,3,0], [7,19,8,1,9,8,2,7,0], [6,16,2,9,6,11,0,6,0], [7,8,11,11,7,7,7,7,0], [5,8,10,3,5,1,1,5,0], [4,10,10,1,4,1,4,4,0], [8,9,14,14,8,8,8,8,0], [3,5,4,1,8,5,0,3,0], [6,11,10,2,6,6,9,6,0], [7,19,11,2,7,5,10,7,0], [6,13,10,2,6,2,2,6,0], [9,12,16,7,9,13,11,9,0], [7,8,16,16,7,3,3,7,0], [5,9,4,4,5,3,1,5,0], [8,17,7,3,16,8,0,8,0], [3,9,2,2,3,0,0,3,0], [9,17,15,3,9,15,5,9,0], [3,4,5,4,4,1,0,3,0], [7,16,12,2,7,4,3,7,0], [3,5,6,2,3,0,0,3,0], [6,11,10,2,6,9,4,6,0], [6,7,13,13,6,2,2,6,0], [10,23,16,3,10,5,5,10,0], [4,5,9,6,6,3,0,4,0], [9,19,8,4,15,7,0,9,0], [10,11,22,22,10,9,9,10,0], [5,20,15,1,5,0,0,5,0], [4,8,11,1,4,4,4,4,0], [7,16,12,2,7,3,4,7,0], [4,9,8,1,4,3,2,4,0], [6,12,5,5,6,3,0,6,0], [7,12,10,3,14,6,0,7,0], [13,24,16,5,26,10,0,13,0], [6,14,4,3,12,11,0,6,0], [10,18,11,7,13,3,0,10,0], [12,22,14,5,23,9,0,12,0], [4,14,9,1,4,0,0,4,0], [6,11,10,2,6,8,5,6,0], [5,11,4,2,10,8,0,5,0], [8,14,13,4,12,8,0,8,0], [10,20,9,6,12,7,0,10,0], [8,17,9,5,8,0,0,8,0], [3,8,1,4,6,7,0,3,0], [8,9,15,15,8,6,6,8,0], [7,8,21,21,7,2,2,7,0], [5,6,15,15,5,0,0,5,0], [5,6,5,5,5,10,10,5,0], [9,10,19,19,9,7,7,9,0], [6,7,17,17,6,1,1,6,0], [10,17,11,11,10,0,0,10,0], [4,9,3,2,5,7,0,4,0], [4,6,5,4,4,4,0,4,0], [4,5,10,9,4,0,0,4,0], [3,4,5,5,3,0,0,3,0], [6,13,5,3,8,0,2,6,10], [3,4,4,5,4,1,0,3,0], [7,25,18,1,13,6,0,7,0], [10,17,8,9,10,4,2,10,0], [9,16,14,4,15,9,0,9,0], [9,10,18,18,9,8,8,9,0], [7,15,6,3,12,7,0,7,0], [3,6,5,1,3,1,3,3,0], [5,9,6,2,10,5,0,5,0], [7,35,28,1,11,4,0,7,0], [4,7,5,1,13,8,0,4,0], [7,19,2,11,7,12,1,7,0], [4,13,9,1,4,0,0,4,7], [4,13,10,1,4,0,0,4,0], [3,8,5,1,3,0,0,3,0], [3,6,2,2,4,0,1,3,5], [4,9,8,1,4,2,3,4,0], [5,7,11,6,5,2,0,5,0], [5,10,5,1,15,10,0,5,0], [4,11,7,1,4,4,5,4,0], [8,17,7,4,10,0,2,8,12], [7,8,9,9,7,14,14,7,0], [4,5,10,6,7,2,0,4,0], [10,26,3,16,10,18,1,10,0], [9,12,22,10,13,10,0,9,0], [3,7,2,2,3,0,0,3,2], [7,9,16,10,10,2,0,7,0], [6,9,6,4,6,3,4,6,0], [4,8,2,5,4,0,0,4,4], [13,37,22,3,17,6,0,13,0], [8,10,23,12,8,1,4,8,0], [6,7,7,7,6,11,11,6,0], [11,29,3,19,11,21,2,11,0], [9,12,8,13,9,9,2,9,0], [4,7,5,2,8,2,0,4,0], [4,11,7,1,4,1,7,4,0], [8,14,6,7,8,4,2,8,0], [6,8,6,5,6,4,5,6,0], [7,13,5,6,7,5,1,7,0], [12,16,25,18,12,3,0,12,0], [8,12,9,5,8,4,8,8,0], [5,6,14,9,5,1,2,5,0], [15,27,45,5,15,27,11,15,0], [10,18,12,4,21,7,0,10,0], [9,17,9,6,11,4,0,9,0], [11,29,16,3,15,6,0,11,0], [18,22,51,30,18,3,6,18,0], [3,6,6,1,3,1,1,3,0], [18,32,13,16,18,13,2,18,0], [6,14,9,2,6,2,3,6,0], [14,24,13,14,14,11,0,14,0], [5,9,5,4,6,2,0,5,0], [6,17,2,9,9,3,0,6,0], [4,11,7,1,4,2,6,4,0], [18,30,20,12,37,15,0,18,0], [8,10,22,13,8,1,2,8,0], [5,8,3,5,5,5,2,5,0], [9,19,7,5,12,8,0,9,0], [4,5,4,4,4,6,5,4,0], [14,28,10,13,14,0,0,14,11], [7,15,6,4,8,6,0,7,0], [7,18,26,2,7,2,1,7,0], [11,19,34,4,11,20,8,11,0], [4,5,5,4,4,3,3,4,0], [5,13,8,1,8,3,0,5,0], [6,7,15,12,6,2,3,6,0], [14,21,17,9,14,6,12,14,0], [3,5,2,4,3,2,0,3,0], [4,7,4,3,6,2,0,4,0], [19,32,21,12,40,17,0,19,0], [10,20,9,7,11,5,0,10,0], [8,21,34,2,8,3,2,8,0], [6,8,6,7,6,2,1,6,0], [4,10,2,3,5,1,0,4,4], [4,5,9,7,5,1,0,4,0], [5,8,5,3,5,4,4,5,0], [4,13,1,9,4,7,0,4,0], [9,25,12,3,11,4,0,9,0], [5,6,7,6,5,4,4,5,0], [6,9,9,5,8,2,0,6,0], [7,11,6,6,7,3,2,7,0], [4,9,5,1,7,3,0,4,0], [9,18,7,6,12,9,0,9,0], [3,7,2,2,3,4,0,3,0], [7,14,6,4,10,7,0,7,0], [6,8,8,5,6,2,1,6,0], [9,24,31,2,9,12,3,9,0], [9,24,43,2,9,4,3,9,0], [5,9,7,2,5,3,2,5,0], [13,20,8,14,13,12,6,13,0], [5,7,7,4,5,1,2,5,0], [21,32,24,13,21,10,18,21,0], [5,10,3,6,5,0,0,5,2], [6,11,6,3,12,6,0,6,0], [20,34,17,18,20,5,4,20,0], [24,40,17,24,24,13,6,24,0], [5,11,14,1,5,6,6,5,0], [7,18,2,21,7,1,7,7,3], [8,10,14,13,8,2,1,8,0], [5,8,6,5,5,2,0,5,0], [19,29,22,12,19,8,16,19,0], [4,6,5,4,6,2,0,4,0], [26,43,25,21,26,6,7,26,0], [11,19,28,4,11,20,12,11,0], [5,10,19,1,5,8,8,5,0], [7,13,6,7,7,3,0,7,0], [36,61,35,29,36,6,11,36,0], [6,9,8,4,6,2,5,6,0], [10,12,18,17,10,4,3,10,0], [14,36,45,4,14,17,2,14,0], [14,22,10,5,16,20,7,14,0], [3,6,5,1,6,2,0,3,0], [11,19,30,4,11,20,10,11,0], [20,34,20,16,20,3,6,20,0], [16,42,51,4,16,19,4,16,0], [15,25,15,12,15,3,4,15,0], [8,21,2,25,8,2,9,8,1], [47,79,37,41,50,15,9,47,0], [25,66,81,6,25,30,7,25,0], [20,30,14,15,24,8,7,20,0]];
end;

cmi2ent:=function(A,B,C,nvars)
  local s1,s2,s3,s4,ineq;
  s1:= Concatenation(A,C);#AC
  s2:= Concatenation(B,C);#BC
  s3:= Concatenation(A,B,C);#ABC
  s4:= AsSet(ShallowCopy(C)); #C
  ineq :=ZeroMutable([1..2^nvars-1]);
  if Size(s1)>0 then
    ineq[set2int(s1)]:=1;
  fi;
  if Size(s2)>0 then
    ineq[set2int(s2)]:=1;
  fi;
  if Size(s3)>0 then
    ineq[set2int(s3)]:=-1;
  fi;
  if Size(s4)>0 then
    ineq[set2int(s4)]:=-1;
  fi;
  return ineq;
end;

DFZNonShannon:=function(idx,los,nvars)
  local NS4,cmi_ineq,A,B,C,D,ent1,ent2,ent3,ent4,ent5,ent6,ent7,ent8,ent9,ent_ineq;
  NS4:=NonShannon4();;
  cmi_ineq:=NS4[idx];
  A:=los[1];
  B:=los[2];
  C:=los[3];
  D:=los[4];
  ent1:=cmi_ineq[1]*cmi2ent(A,B,[],nvars);
  ent2:=-cmi_ineq[2]*cmi2ent(A,B,C,nvars);
  ent3:=-cmi_ineq[3]*cmi2ent(A,C,B,nvars);
  ent4:=-cmi_ineq[4]*cmi2ent(B,C,A,nvars);
  ent5:=-cmi_ineq[5]*cmi2ent(A,B,D,nvars);
  ent6:=-cmi_ineq[6]*cmi2ent(A,D,B,nvars);
  ent7:=-cmi_ineq[7]*cmi2ent(B,D,A,nvars);
  ent8:=-cmi_ineq[8]*cmi2ent(C,D,[],nvars);
  ent9:=-cmi_ineq[9]*cmi2ent(C,D,A,nvars);
  ent_ineq:=ent1+ent2+ent3+ent4+ent5+ent6+ent7+ent8+ent9;
  return ent_ineq;
end;

ZYNonShannon:=function(los,nvars)
  local cmi_ineq,A,B,C,D,ent1,ent2,ent3,ent4,ent5,ent6,ent7,ent8,ent9,ent_ineq;
  cmi_ineq:=[1,2,1,1,1,0,0,1,0];
  A:=los[1];
  B:=los[2];
  C:=los[3];
  D:=los[4];
  ent1:=cmi_ineq[1]*cmi2ent(A,B,[],nvars);
  ent2:=-cmi_ineq[2]*cmi2ent(A,B,C,nvars);
  ent3:=-cmi_ineq[3]*cmi2ent(A,C,B,nvars);
  ent4:=-cmi_ineq[4]*cmi2ent(B,C,A,nvars);
  ent5:=-cmi_ineq[5]*cmi2ent(A,B,D,nvars);
  ent6:=-cmi_ineq[6]*cmi2ent(A,D,B,nvars);
  ent7:=-cmi_ineq[7]*cmi2ent(B,D,A,nvars);
  ent8:=-cmi_ineq[8]*cmi2ent(C,D,[],nvars);
  ent9:=-cmi_ineq[9]*cmi2ent(C,D,A,nvars);
  ent_ineq:=ent1+ent2+ent3+ent4+ent5+ent6+ent7+ent8+ent9;
  return ent_ineq;
end;
# SSShannon:=function(Asets,nvars)
# # Shannon + network constraints + capacity caps on edge rates
# local ShOB,i,linrows,con,conlin,j,conineq;
#   ShOB:=GenShannonUnBounded(nvars);
#   i:=Size(ShOB[1])+1;
#   linrows:=[];
#   # node constraints
#   for con in ncinstance[1] do
#     conlin:=ZeroMutable([1..2^ncinstance[3]-1]);
#     conlin[set2int(con[1])]:=1;
#     conlin[set2int(con[2])]:=-1;
#     Append(ShOB[1],[conlin]);
#     Append(ShOB[2],[0]);
#     Append(linrows,[i]);
#     i:=i+1;
#   od;
#   # source independence
#   conlin:= ZeroMutable([1..2^ncinstance[3]-1]);
#   for j in [1..ncinstance[2]] do
#   conlin[set2int([j])]:=1;
#   od;
#   conlin[set2int([1..ncinstance[2]])]:=-1;
#   Append(ShOB[1],[conlin]);
#   Append(ShOB[2],[0]);
#   Append(linrows,[i]);
#   i:=i+1;
#   # source and edge rates, here we substitute edge capacities
#   for j in [1..Size(ShOB[1])] do
#   ShOB[1][j]:=Concatenation(ZeroMutable([1..ncinstance[3]]),ShOB[1][j]);
#   od;
#   for j in [1..ncinstance[2]] do # source rate ineq
#     conineq:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
#     conineq[j]:=1;
#     conineq[ncinstance[3]+set2int([j])]:=-1;
#     Append(ShOB[1],[conineq]);
#     Append(ShOB[2],[0]);
#     conineq:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
#     conineq[j]:=-1; # non-negative
#     Append(ShOB[1],[conineq]);
#     Append(ShOB[2],[0]);
#   od;
#   for j in [ncinstance[2]+1..ncinstance[3]] do # edge rate ineq + capacity ineq
#     conineq:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
#     conineq[j]:=-1;
#     conineq[ncinstance[3]+set2int([j])]:=1;
#     Append(ShOB[1],[conineq]);
#     Append(ShOB[2],[0]);
#     conineq:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
#     conineq[j]:=-1; # non-negative
#     Append(ShOB[1],[conineq]);
#     Append(ShOB[2],[0]);
#     conineq:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
#     conineq[j]:=1; # capacity bound
#     Append(ShOB[1],[conineq]);
#     Append(ShOB[2],[caps[j-ncinstance[2]]]);
#   od;
#   return [ShOB[1],ShOB[2],linrows];
# end;

RRparse:=function(nc,rr)
  local displaystr,row,i;
  displaystr:="";
  for row in rr do
    if row{[nc[2]+1..nc[3]]}=ZeroMutable([nc[2]+1..nc[3]]) then
      displaystr:=Concatenation(displaystr,"0 ");
    else
      for i in [nc[2]+1..nc[3]] do
        if -row[i]>0 then
          if -row[i]=1 then
            displaystr:=Concatenation(displaystr,"+ R",String(i)," ");
          else
            displaystr:=Concatenation(displaystr,"+",String(-row[i])," R",String(i)," ");
          fi;
        elif -row[i]<0 then
          if -row[i]=-1 then
            displaystr:=Concatenation(displaystr,"- R",String(i)," ");
          else
            displaystr:=Concatenation(displaystr,String(-row[i])," R",String(i)," ");
          fi;
        fi;
      od;
    fi;
    displaystr:=Concatenation(displaystr,">= ");
    if row{[1..nc[2]]}=ZeroMutable([1..nc[2]]) then
      displaystr:=Concatenation(displaystr,"0 ");
    else
      for i in [1..nc[2]] do
        if row[i]>0 then
          if row[i]=1 then
            displaystr:=Concatenation(displaystr,"+ w",String(i)," ");
          else
            displaystr:=Concatenation(displaystr,"+",String(row[i])," w",String(i)," ");
          fi;
        elif row[i]<0 then
          if row[i]=-1 then
            displaystr:=Concatenation(displaystr,"- w",String(i)," ");
          else
            displaystr:=Concatenation(displaystr,String(row[i])," w",String(i)," ");
          fi;
        fi;
      od;
    fi;
    displaystr:=Concatenation(displaystr,"\n");
  od;
  return displaystr;
end;





SSShareSizesUB:=function(Asets,nvars)
end;


SScons:=function(Asets,nvars)
  # loop over all subsets s of [1..nvars]
  # if s doesnt contain any set in Asets, h(s,1) = h(s) + s(1)
  local cons,itr,s,bads,a,conlin;
  cons:=[];
  itr:=IteratorOfCombinations([2..nvars]);
  for s in itr do
    if Size(s)>0 then
      bads:=true;
      for a in Asets do
        if IsSubset(s,a) then
          bads:=false;
          break;
        fi;
      od;
      if bads=true then
        conlin:=ZeroMutable([1..2^nvars-1]);
        conlin[set2int(Concatenation([1],s))]:=-1;
        conlin[set2int([1])]:=1;
        conlin[set2int(s)]:=1;
        Append(cons,[conlin]);
      fi;
    fi;
  od;
  for a  in Asets do
    conlin:=ZeroMutable([1..2^nvars-1]);
    conlin[set2int(Concatenation([1],a))]:=-1;
    conlin[set2int(a)]:=1;
    Append(cons,[conlin]);
  od;
  return cons;
end;

NCSymmetryCons:=function(ncinstance)
local NSG,pset,pset_orbs,cons,conlin,orb,j;
  NSG:=NetSymGroup(ncinstance);
  # construct orbitwise inequalities
  pset:=Combinations([1..ncinstance[3]]);
  pset:=pset{[2..Size(pset)]};
  pset_orbs:=OrbitsDomain(NSG,pset,OnSets);
  cons:=[];
  #Display(pset_orbs);
  #Display(Size(pset_orbs));
  for orb in pset_orbs do
    if Size(orb[1])<ncinstance[3] and Size(orb)>1 then
      for j in [1..Size(orb)-1] do
        conlin:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
        conlin[set2int(orb[j])+ncinstance[3]]:=1;
        conlin[set2int(orb[j+1])+ncinstance[3]]:=-1;
        Append(cons,[conlin]);
      od;
    fi;
  od;
  return cons;
end;



SSSymmetryCons:=function(Asets,nvars)
  local SSG,pset,pset_orbs,cons,conlin,orb,j;
    SSG:=SSSymGroup(Asets,nvars);
    # construct orbitwise inequalities
    pset:=Combinations([1..nvars]);
    pset:=pset{[2..Size(pset)]};
    pset_orbs:=OrbitsDomain(SSG,pset,OnSets);
    cons:=[];
    #Display(pset_orbs);
    #Display(Size(pset_orbs));
    for orb in pset_orbs do
      if Size(orb[1])<nvars and Size(orb)>1 then
        for j in [1..Size(orb)-1] do
          conlin:=ZeroMutable([1..2^nvars]);
          conlin[set2int(orb[j])+1]:=1;
          conlin[set2int(orb[j+1])+1]:=-1;
          Append(cons,[conlin]);
        od;
      fi;
    od;
    return cons;
end;

GGSymmetryCons:=function(G)
  local GGG,pset,pset_orbs,cons,conlin,orb,j;
    GGG:=GGSymGroup(G);
    # construct orbitwise inequalities
    pset:=Combinations([1..Size(G[1])]);
    pset:=pset{[2..Size(pset)]};
    pset_orbs:=OrbitsDomain(GGG,pset,OnSets);
    cons:=[];
    #Display(pset_orbs);
    #Display(Size(pset_orbs));
    for orb in pset_orbs do
      if Size(orb[1])<Size(G[1]) and Size(orb)>1 then
        for j in [1..Size(orb)-1] do
          conlin:=ZeroMutable([1..2^Size(G[1])-1]);
          conlin[set2int(orb[j])]:=1;
          conlin[set2int(orb[j+1])]:=-1;
          Append(cons,[conlin]);
        od;
      fi;
    od;
    return cons;
end;

SSShannonWC:=function(Asets,nvars)
  local ShOB,A,b,linrows,v,conineq,conlin,i,vA,sc,a;
  ShOB:=GenShannonUnBounded(nvars);
  A:=ShOB[1];
  b:=ShOB[2];
  sc:=SScons(Asets,nvars);
  linrows:=[1..Size(sc)]+Size(A);
  Append(A,sc);
  Append(b,ZeroMutable([1..Size(sc)]));
  vA:= [];
  for a in A do
    Append(vA,[Concatenation([0],a)]);
  od;
  for i in [1..nvars] do
    conineq:= ZeroMutable([1..2^nvars]);
    conineq[1]:=-1;
    conineq[set2int([i])+1]:=1;
    Append(vA,[conineq]);
    Append(b,[0]);
  od;
  conlin:=ZeroMutable([1..2^nvars]);
  conlin[set2int([1])+1]:=1;
  Append(vA,[conlin]);
  Append(b,[1]);
  Append(linrows,[Size(vA)]);
  return [vA,b,linrows];
end;


GGShannon:=function(G)
  local ShOB,A,b,linrows,v,conineq,conlin,i;
  ShOB:=GenShannonUnBounded(Size(G[1]));
  A:=ShOB[1];
  b:=ShOB[2];
  linrows:=[];
  # h(i) <=1 for each vertex i
  for v in G[1] do
    conineq:= ZeroMutable([1..2^Size(G[1])-1]);
    conineq[set2int([v])]:=1;
    Append(A,[conineq]);
    Append(b,[1]);
  od;
  # h(i|In(i))=0 for each vertex i
  i:=Size(A)+1;
  for v in RecNamesInt(G[2]) do
    conlin:=ZeroMutable([1..2^Size(G[1])-1]);
    conlin[set2int(G[2].(v))]:=1;
    conlin[set2int(Concatenation([v],G[2].(v)))]:=-1;
    Append(A,[conlin]);
    Append(b,[0]);
    Append(linrows,[i]);
    i:=i+1;
  od;
  return [A,b,linrows];
end;



OnIneq:=function(ineq,g)
  local a,b,permidx,rineq;
  b:=ineq[Size(ineq)];
  a:=ineq{[1..Size(ineq)-1]};
  permidx:=OnTuples([1..Size(a)],g);
  rineq:=Concatenation(a{permidx},[b]);
  return rineq;
end;

OnIneqSet:=function(ineqset,g)
  local rineqset, ineq;
  rineqset:=[];
  for ineq in ineqset do
    Append(rineqset,[OnIneq(ineq,g)]);
  od;
  return AsSet(rineqset);
end;

IneqPermSym:=function(A,b)
  local N,tupset,i,ab;
  N:=Size(A[1]);
  tupset:=[];
  for i in [1..Size(A)] do
    ab:= Concatenation(A[i],[b[i]]);
    Append(tupset,[ab]);
  od;
  tupset:=AsSet(tupset);
  return Stabilizer(SymmetricGroup(N),tupset,OnIneqSet);
end;

NCpolytope_fwrite:=function(ncinstance,fname)
  local rlist,A,b,linrows,mtx,i;
  rlist:=NCShannonBounded(ncinstance);
  A:=rlist[1];
  b:=rlist[2];
  linrows:=rlist[3];
  mtx:=[];
  for i in [1..Size(A)] do
    Append(mtx,[Concatenation([b[i]],-A[i])]);
  od;
  writeinefile(fname,linrows,mtx);
end;

NCRateRegionOB2:=function(ncinstance,usesym,optargs)
  local rlist,A,b,linrows,G,rlist1,ineq,ineqorb,row,rrA,rrb,onemap,nslist,idx,nsrec,los,lolos,Oi,O,trans_ineq;
  rlist:=NCShannonBounded(ncinstance);
  A:=rlist[1];
  b:=rlist[2];
  linrows:=rlist[3];
  #Comnpute symmetry group of ncinstance
  if usesym=false then
    G:=Group([()]);
  else
    G:=NetSymGroup(ncinstance);
  fi;
  #if non-shannons are specified for some subsets, include all permutations of them
  if Size(optargs)>0 then
    nslist:=[];
    nsrec:=optargs[1];
    for idx in RecNamesInt(nsrec) do
      lolos:=nsrec.(idx);
      for los in lolos do
        if idx = 1 then
          ineq:= ZYNonShannon(los,ncinstance[3]);
          ineqorb:=Orbit(G,ineq,OnEntropySpace);
          Append(nslist,ineqorb);
        else
          ineq:= DFZNonShannon(idx-1,los,ncinstance[3]);
          ineqorb:=Orbit(G,ineq,OnEntropySpace);
          Append(nslist,ineqorb);
        fi;
      od;
    od;
    Append(A,nslist);
    Append(b,ZeroMutable([1..Size(nslist)]));
  fi;
  rlist1:=symCHM(A,b,linrows,ncinstance[3],G,OnProjPts,OnProjIneq,false);
  Display(Concatenation("stats:  No. of LPs solved = ",String(rlist1[3][1]),", \n\t No. of facets = ",String(Size(rlist1[2])),", \n\tDD stepsizes beyond initial hull = ",String(rlist1[3][2]) ));
  rrA:=[];
  rrb:=[];
  for row in rlist1[2] do
    # find the bounding sum-to-one inequality
    onemap := function ( x ) return 1; end;
    if not row=List([1..Size(row)],onemap) then
      Append(rrA,[row{[1..Size(row)-1]}]);
      Append(rrb,[row[Size(row)]]);
    fi;
  od;
  # inequality transversal
  trans_ineq:= [];
  Oi:=OrbitsDomain(G,rrA,OnProjIneq);
  for O in Oi do
    Append(trans_ineq,[O[1]]);
  od;
  return [trans_ineq, RRparse(ncinstance,trans_ineq)];#[rlist1[1],rlist1[2]];
end;

InstallGlobalFunction(NCRateRegionOB,
function(ncinstance,usesym,optargs)
  local rlist,A,b,linrows,G,rlist1,ineq,ineqorb,row,rrA,rrb,onemap,nslist,idx,nsrec,los,lolos,Oi,O,trans_ineq;
  rlist:=NCShannonBounded(ncinstance);
  A:=rlist[1];
  b:=rlist[2];
  linrows:=rlist[3];
  #Comnpute symmetry group of ncinstance
  if usesym=false then
    G:=Group([()]);
  else
    G:=NetSymGroup(ncinstance);
  fi;
  #if non-shannons are specified for some subsets, include all permutations of them
  if Size(optargs)>0 then
    nslist:=[];
    nsrec:=optargs[1];
    for idx in RecNamesInt(nsrec) do
      lolos:=nsrec.(idx);
      for los in lolos do
        if idx = 1 then
          ineq:= ZYNonShannon(los,ncinstance[3]);
          ineqorb:=Orbit(G,ineq,OnEntropySpace);
          Append(nslist,ineqorb);
        else
          ineq:= DFZNonShannon(idx-1,los,ncinstance[3]);
          ineqorb:=Orbit(G,ineq,OnEntropySpace);
          Append(nslist,ineqorb);
        fi;
      od;
    od;
    Append(A,nslist);
    Append(b,ZeroMutable([1..Size(nslist)]));
  fi;
  rlist1:=symCHM(A,b,linrows,ncinstance[3],G,OnProjPts,OnProjIneq,false);
  Display(Concatenation("stats:  No. of LPs solved = ",String(rlist1[3][1]),", \n\t No. of facets = ",String(Size(rlist1[2])),", \n\tDD stepsizes beyond initial hull = ",String(rlist1[3][2]) ));
  rrA:=[];
  rrb:=[];
  for row in rlist1[2] do
    # find the bounding sum-to-one inequality
    onemap := function ( x ) return 1; end;
    if not row=List([1..Size(row)],onemap) then
      Append(rrA,[row{[1..Size(row)-1]}]);
      Append(rrb,[row[Size(row)]]);
    fi;
  od;
  # inequality transversal
  trans_ineq:= [];
  Oi:=OrbitsDomain(G,rrA,OnProjIneq);
  for O in Oi do
    Append(trans_ineq,[O[1]]);
  od;
  return [trans_ineq, RRparse(ncinstance,trans_ineq)];#[rlist1[1],rlist1[2]];
end);

# NCRateRegionOB2:=function(ncinstance,usesym,optargs)
#   local rlist,A,b,linrows,G,rlist1,ineq,ineqorb,row,rrA,rrb,onemap,nslist,idx,nsrec,los,lolos,Oi,O,trans_ineq;
#   rlist:=NCShannonBounded(ncinstance);
#   A:=rlist[1];
#   b:=rlist[2];
#   linrows:=rlist[3];
#   #Comnpute symmetry group of ncinstance
#   if usesym=false then
#     G:=Group([()]);
#   else
#     G:=NetSymGroup(ncinstance);
#   fi;
#   #if non-shannons are specified for some subsets, include all permutations of them
#   if Size(optargs)>0 then
#     nslist:=[];
#     nsrec:=optargs[1];
#     for idx in RecNamesInt(nsrec) do
#       lolos:=nsrec.(idx);
#       for los in lolos do
#         if idx = 1 then
#           ineq:= ZYNonShannon(los,ncinstance[3]);
#           ineqorb:=Orbit(G,ineq,OnEntropySpace);
#           Append(nslist,ineqorb);
#         else
#           ineq:= DFZNonShannon(idx-1,los,ncinstance[3]);
#           ineqorb:=Orbit(G,ineq,OnEntropySpace);
#           Append(nslist,ineqorb);
#         fi;
#       od;
#     od;
#     Append(A,nslist);
#     Append(b,ZeroMutable([1..Size(nslist)]));
#   fi;
#   rlist1:=symCHM(A,b,linrows,ncinstance[3],G,OnProjPts,OnProjIneq);
#   Display(Concatenation("stats:  No. of LPs solved = ",String(rlist1[3][1]),", \n\t No. of facets = ",String(Size(rlist1[2])),", \n\tDD stepsizes beyond initial hull = ",String(rlist1[3][2]) ));
#   rrA:=[];
#   rrb:=[];
#   for row in rlist1[2] do
#     # find the bounding sum-to-one inequality
#     onemap := function ( x ) return 1; end;
#     if not row=List([1..Size(row)],onemap) then
#       Append(rrA,[row{[1..Size(row)-1]}]);
#       Append(rrb,[row[Size(row)]]);
#     fi;
#   od;
#   # inequality transversal
#   trans_ineq:= [];
#   Oi:=OrbitsDomain(G,rrA,OnProjIneq);
#   for O in Oi do
#     Append(trans_ineq,[O[1]]);
#   od;
#   return [trans_ineq, RRparse(ncinstance,trans_ineq)];#[rlist1[1],rlist1[2]];
# end;

InstallGlobalFunction(NCSumRateUB,
function(ncinstance,caps,optargs)
  local rlist,rlist1,rlist2,obj,s,onemap,nslist,idx,nsrec,lolos,los,A,b,opt,linrows,symcons,maxkn,optk,i,ns,G,ineq,ineqorb;
  rlist:= NCShannonCaps(ncinstance,caps);
  A:=rlist[1];
  b:=rlist[2];
  linrows:=rlist[3];
  G:=NetSymGroup(ncinstance);
  nslist:=[];
  if Size(optargs)>0 then
    nsrec:=optargs[1];
    for idx in RecNamesInt(nsrec) do
      lolos:=nsrec.(idx);
      for los in lolos do
        if idx = 1 then
          ineq:= ZYNonShannon(los,ncinstance[3]);
          ineqorb:=Orbit(G,ineq,OnEntropySpace);
          Append(nslist,ineqorb);
        else
          ineq:= DFZNonShannon(idx-1,los,ncinstance[3]);
          ineqorb:=Orbit(G,ineq,OnEntropySpace);
          Append(nslist,ineqorb);
        fi;
      od;
    od;
    Append(A,nslist);
    Append(b,ZeroMutable([1..Size(nslist)]));
  fi;
  for ns in nslist do
    Append(A,[Concatenation(ZeroMutable([1..ncinstance[3]]),ns)]);
    Append(b,[0]);
  od;
  Display(Concatenation("Original LP dimension...",String(Size(A[1])-RankMat(A{linrows})-1)));
  symcons:=NCSymmetryCons(ncinstance);
  Display(Concatenation("LP dimension after considering symmetries...",String(Size(A[1])-RankMat(Concatenation(A{linrows},symcons))-1)));
  if Size(symcons)>0 then
    Append(linrows,[Size(A)+1..Size(A)+Size(symcons)]);
    Append(A,symcons);
    Append(b,ZeroMutable([1..Size(symcons)]));
  fi;
  onemap := function ( x ) return 1; end;
  obj:= Concatenation(List([1..ncinstance[2]],onemap),ZeroMutable([1..Size(A[1])-ncinstance[2]]));
  rlist1:=LoadQSLP(obj,A,b,linrows,qs_exec);
  s:= rlist1[1];
  #isplayLPQS(s);
  SolveQSLP(s,[]);
  rlist2:=GetQSLPsol_primal(s);
  FlushQSLP(s);
  # opt := rlist2[5];
  # optk:=rlist2[3]/ncinstance[2];
  # Display(optk);
  # Display(opt{[1..ncinstance[3]]});
  # maxkn:=0;
  # for i in [ncinstance[2]+1..ncinstance[3]] do
  #   maxkn:=Maximum(optk/opt[i],maxkn);
  # od;
  return rlist2[3];
end);


InstallGlobalFunction(SSWorstInfoRatioLB,
function(Asets,nvars,optargs)
  local rlist,obj,rlist1,s,rlist2,A,b,linrows,symcons,nslist,ns,nsrec,idx,lolos,los;
  rlist:=SSShannonWC(Asets,nvars);
  A:=rlist[1];
  b:=rlist[2];
  linrows:=rlist[3];
  nslist:=[];
  if Size(optargs)>0 then
    nsrec:=optargs[1];
    for idx in RecNamesInt(nsrec) do
      lolos:=nsrec.(idx);
      for los in lolos do
        if idx = 1 then
          Append(nslist,[ZYNonShannon(los,nvars)]);
        else
          Append(nslist,[DFZNonShannon(idx-1,los,nvars)]);
        fi;
      od;
    od;
  fi;
  for ns in nslist do
    Append(A,[Concatenation([0],ns)]);
    Append(b,[0]);
  od;
  Display(Concatenation("Original LP dimension...",String(Size(A[1])-RankMat(A{linrows})-1)));
  symcons:=SSSymmetryCons(Asets,nvars);
  Display(Concatenation("LP dimension after considering symmetries...",String(Size(A[1])-RankMat(Concatenation(A{linrows},symcons))-1)));
  if Size(symcons)>0 then
    Append(linrows,[Size(A)+1..Size(A)+Size(symcons)]);
    Append(A,symcons);
    Append(b,ZeroMutable([1..Size(symcons)]));
  fi;
  obj:= ZeroMutable([1..2^nvars]);;
  obj[1]:=-1;
  rlist1:=LoadQSLP(obj,A,b,linrows,qs_exec);
  s:= rlist1[1];
  #DisplayLPQS(s);
  SolveQSLP(s,[]);
  rlist2:=GetQSLPsol_primal(s);
  FlushQSLP(s);
  return -rlist2[3];
end);

InstallGlobalFunction(GGnumberUB,
function(G,optargs)
  local rlist,obj,rlist1,s,rlist2,A,b,linrows,nslist,ns,idx,nsrec,symcons,los,lolos;
  rlist:=GGShannon(G);
  A:=rlist[1];
  b:=rlist[2];
  linrows:=rlist[3];
  # Add nonshannons
  nslist:=[];
  if Size(optargs)>0 then
    nsrec:=optargs[1];
    for idx in RecNamesInt(nsrec) do
      lolos:=nsrec.(idx);
      for los in lolos do
        if idx = 1 then
          Append(nslist,[ZYNonShannon(los,Size(G[1]))]);
        else
          Append(nslist,[DFZNonShannon(idx-1,los,Size(G[1]))]);
        fi;
      od;
    od;
  fi;
  for ns in nslist do
    Append(A,[ns]);
    Append(b,[0]);
  od;
  # Add symmetry constraints

  Display(Concatenation("Original LP dimension...",String(Size(A[1])-RankMat(A{linrows})-1)));
  symcons:=GGSymmetryCons(G);
  Display(Concatenation("LP dimension after considering symmetries...",String(Size(A[1])-RankMat(Concatenation(A{linrows},symcons))-1)));
  if Size(symcons)>0 then
    Append(linrows,[Size(A)+1..Size(A)+Size(symcons)]);
    Append(A,symcons);
    Append(b,ZeroMutable([1..Size(symcons)]));
  fi;
  obj:= ZeroMutable([1..2^Size(G[1])-1]);;
  obj[set2int(G[1])]:=1;
  rlist1:=LoadQSLP(obj,A,b,linrows,qs_exec);
  s:= rlist1[1];
  #DisplayLPQS(s);
  SolveQSLP(s,[]);
  rlist2:=GetQSLPsol_primal(s);
  FlushQSLP(s);
  return rlist2[3];
end);

# higher symmetries of classical/quantum entropy connection
s4rays:=[ [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 ], [ 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1 ],
  [ 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1 ], [ 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1 ],
  [ 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1 ], [ 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1 ],
  [ 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 ], [ 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1 ],
  [ 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1 ], [ 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 ],
  [ 0, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2 ], [ 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2 ],
  [ 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2 ], [ 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 ],
  [ 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 4, 4, 4, 4 ], [ 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2 ],
  [ 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1 ], [ 1, 1, 2, 1, 2, 2, 2, 0, 1, 1, 2, 1, 2, 2, 2 ],
  [ 1, 2, 3, 1, 2, 3, 3, 1, 2, 3, 3, 2, 3, 3, 3 ], [ 2, 2, 3, 2, 3, 4, 4, 2, 3, 3, 4, 3, 4, 4, 4 ],
  [ 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1 ], [ 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 3 ],
  [ 2, 2, 3, 2, 3, 3, 4, 2, 3, 4, 4, 3, 4, 4, 4 ], [ 2, 2, 4, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 4 ],
  [ 1, 1, 2, 0, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2 ], [ 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 ],
  [ 1, 0, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2 ], [ 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 3, 3, 3, 3, 3 ],
  [ 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2 ], [ 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2 ],
  [ 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2 ], [ 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2 ],
  [ 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 3, 3, 3, 3, 3 ], [ 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2 ],
  [ 2, 2, 3, 2, 4, 3, 4, 2, 3, 3, 4, 3, 4, 4, 4 ], [ 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2 ],
  [ 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 ], [ 2, 2, 3, 2, 3, 3, 4, 2, 4, 3, 4, 3, 4, 4, 4 ],
  [ 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2 ], [ 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2 ],
  [ 2, 1, 3, 1, 3, 2, 3, 1, 3, 2, 3, 2, 3, 3, 3 ] ];

  s3rays:=[[ 1, 1, 1, 1, 1, 1, 1] ,
   [1, 0, 1, 1, 1, 1, 1 ],
   [1, 1, 1, 0, 1, 1, 1 ],
   [0, 0, 0, 1, 1, 1, 1 ],
   [0, 1, 1, 0, 0, 1, 1 ],
   [1, 0, 1, 0, 1, 0, 1 ],
   [0, 1, 1, 1, 1, 1, 1 ],
   [1, 1, 2, 1, 2, 2, 2]];

  s2rays:=[[1,1,1],[0,1,1],[1,0,1]];

H4:=Group([ (5,6),
 (4,5),
 (2,4),
 (3,17)(7,14)(10,26)(13,29)(15,23)(19,28)(24,35)(25,27)(30,36)(32,39),
 (3,10)(7,14)(11,18)(13,30)(15,24)(16,31)(17,26)(19,28)(21,37)(23,35)(25,27)(29,36)(32,39)(33,41),
 (3,9)(8,10)(12,13)(14,21)(18,25)(20,23)(28,33)(30,40)(31,39)(35,38),
 (1,22)(3,10)(7,11)(8,9)(14,18)(15,24)(16,19)(21,25)(27,37)(28,31)(29,36)(32,41)(33,39),
 (4,6),
 (1,22)(7,18)(8,9)(11,14)(13,30)(16,28)(17,26)(19,31)(21,27)(23,35)(25,37)(32,33)(39,41),
 (7,21)(8,26)(9,17)(12,29)(15,20)(18,27)(19,33)(24,38)(31,32)(36,40),
 (8,17)(9,26)(11,25)(12,36)(14,37)(15,38)(16,39)(20,24)(28,41)(29,40)]);

H3:=Group([ (5,6),
 (4,5),
 (1,8),
 (3,7),
 (2,3),
 (4,6),
 (2,7)]);

H2:=Group([ (2,3),
 (1,2),
 (1,3)]);


if not IsBound(perm2bj) then
  perm2bj:=function(g,maxi)
     return List([1..maxi],x->x^g);
  end;
fi;

rayperm2mat:=function(g,raylist)
  local bj,raylistT,mat,i,j,vec,row;
  # find the bijection
  bj:=perm2bj(g,Size(raylist));
  raylistT:=TransposedMat(raylist);
  mat:=[];
  # for each row of matrix construct equations
  for i in [1..Size(raylist[1])] do
    vec:=[];
    for j in [1..Size(raylist)] do
      Append(vec,[ raylist[bj[j]][i] ]);
    od;
    row:=SolutionMat(raylistT,vec);
    Append(mat,[row]);
  od;
  return mat;
end;

ExpandLinSym:=function(M,n,nx)
  # expand  n-variable linear symmetry to form nx-variable linear symmetry
  # M is 2^n-1 X 2^n-1 matrix
  # returns 2^nx-1 X 2^nx-1 matrix
  local Mx, i,row;
  Mx:=[];
  for i in [1..2^nx-1] do
    if i > 2^n-1 then
      row:=ZeroMutable([1..2^nx-1]);
      row[i]:=1;
    else
      row:= Concatenation(M[i],ZeroMutable([1..2^n-1]));
    fi;
    Append(Mx,[row]);
  od;
  return Mx;
end;


HM4gens:=[ [ [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0 ],
      [ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0 ],
      [ 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0 ],
      [ 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, -1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, -1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 ] ],
  [ [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0 ],
      [ 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0 ],
      [ 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0 ],
      [ 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 ] ],
  [ [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, -1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 ] ],
  [ [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0 ],
      [ 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0 ],
      [ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0 ],
      [ 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 ] ],
  [ [ 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1, 0 ],
      [ 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, -1, -1, 0 ],
      [ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, -1, 0, 1, -1, 0 ],
      [ 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 1, 0, -1, 1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 ] ],
  [ [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, -1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 ] ],
  [ [ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0 ],
      [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0 ],
      [ 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 1 ],
      [ 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 0 ],
      [ 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0, -1, 1 ],
      [ 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, -1, 0, -1, 0, 1 ],
      [ 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, -1, 0, -1, -1, 2 ],
      [ 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 1, 0, 1, 0, 0, -1, 0, 1, 0, 0, 0, 0, -1, 1 ],
      [ 1, 0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, 1 ],
      [ 1, 1, 0, 1, 0, 0, -1, 1, 0, 0, 0, 0, -1, -1, 2 ],
      [ 0, 0, 1, 1, 0, 0, -1, 1, 0, 0, -1, 0, 0, 0, 1 ],
      [ 1, 1, 0, 1, 0, 0, -1, 1, 0, 0, -1, 0, 0, -1, 2 ],
      [ 1, 1, 0, 1, 0, 0, -1, 1, 0, 0, -1, 0, -1, 0, 2 ],
      [ 1, 1, 0, 1, 0, 0, -1, 1, 0, 0, -1, 0, -1, -1, 3 ] ],
  [ [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0 ],
      [ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0 ],
      [ 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0 ],
      [ 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, -1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, -1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 ] ],
  [ [ 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1, 0, 0 ],
      [ 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1, 1 ],
      [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0 ],
      [ 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, -1, 0, 0, -1, 1 ],
      [ 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, -1, 0, -1, 0, 1 ],
      [ 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, -1, 0, -1, -1, 2 ],
      [ 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 1, 0, 1, 0, 0, -1, 0, 1, 0, 0, 0, 0, -1, 1 ],
      [ 0, 1, 0, 0, 1, 0, -1, 1, 0, 0, 0, 0, -1, 0, 1 ],
      [ 1, 1, 0, 1, 0, 0, -1, 1, 0, 0, 0, 0, -1, -1, 2 ],
      [ 1, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1, 1, 0, 0, 1 ],
      [ 1, 1, 0, 1, 0, 0, -1, 1, 0, 0, -1, 0, 0, -1, 2 ],
      [ 1, 1, 0, 1, 0, 0, -1, 1, 0, 0, -1, 0, -1, 0, 2 ],
      [ 1, 1, 0, 1, 0, 0, -1, 1, 0, 0, -1, 0, -1, -1, 3 ] ],
  [ [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, -1, 0, 0 ],
      [ 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, -1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 ] ],
  [ [ 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0 ],
      [ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, -1, 0 ],
      [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0 ],
      [ 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, -1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 ] ] ];

HM3gens:=[ [ [ 1, 0, 0, 0, -1, 1, 0 ], [ 0, 1, 0, 0, 1, -1, 0 ], [ 0, 0, 1, 0, 0, 0, 0 ], [ 0, 0, 0, 1, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 1, 0 ],
      [ 0, 0, 0, 0, 1, 0, 0 ], [ 0, 0, 0, 0, 0, 0, 1 ] ], [ [ 1, 0, 0, 0, 0, 0, 0 ], [ 0, 1, -1, 0, 1, 0, 0 ], [ 0, 0, 0, 0, 1, 0, 0 ], [ 0, 0, 1, 1, -1, 0, 0 ],
      [ 0, 0, 1, 0, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 1, 0 ], [ 0, 0, 0, 0, 0, 0, 1 ] ], [ [ 1, 0, 0, 0, 0, 0, 0 ], [ 0, 1, 0, 0, 0, 0, 0 ],
      [ 1, 1, 0, 1, -1, -1, 1 ], [ 0, 0, 0, 1, 0, 0, 0 ], [ 1, 1, -1, 1, 0, -1, 1 ], [ 1, 1, -1, 1, -1, 0, 1 ], [ 1, 1, -1, 1, -1, -1, 2 ] ],
  [ [ 0, 0, 1, 1, 0, -1, 0 ], [ 0, 1, 0, 0, 0, 0, 0 ], [ 0, 0, 1, 0, 0, 0, 0 ], [ 1, 0, -1, 0, 0, 1, 0 ], [ 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 1, 0 ], [ 0, 0, 0, 0, 0, 0, 1 ] ], [ [ 1, 0, 0, 0, 0, 0, 0 ], [ 0, 0, 1, 1, -1, 0, 0 ], [ 0, 0, 1, 0, 0, 0, 0 ], [ 0, 1, -1, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 1, 0, 0 ], [ 0, 0, 0, 0, 0, 1, 0 ], [ 0, 0, 0, 0, 0, 0, 1 ] ], [ [ 1, 0, -1, 0, 0, 1, 0 ], [ 0, 1, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 1, 0 ], [ 0, 0, 1, 1, 0, -1, 0 ], [ 0, 0, 0, 0, 1, 0, 0 ], [ 0, 0, 1, 0, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 0, 1 ] ],
  [ [ 0, 1, 0, 0, 1, -1, 0 ], [ 1, 0, 0, 0, -1, 1, 0 ], [ 0, 0, 1, 0, 0, 0, 0 ], [ 0, 0, 0, 1, 0, 0, 0 ],
      [ 0, 0, 0, 0, 1, 0, 0 ], [ 0, 0, 0, 0, 0, 1, 0 ], [ 0, 0, 0, 0, 0, 0, 1 ] ] ];

HM2gens:=[ [ [ 0, 1, 0 ], [ 1, 0, 0 ], [ 0, 0, 1 ] ], [ [ -1, -1, 2 ], [ 0, 1, 0 ], [ 0, 0, 1 ] ],
  [ [ 1, 0, 0 ], [ -1, -1, 2 ], [ 0, 0, 1 ] ] ];


  RecSetwise:=function ( r, s )
      local  k, l;
      l := [  ];
      for k  in s  do
          Append( l, [ r.(k) ] );
      od;
      return l;
  end;

  ray_delminor:=function ( ray, n, set )
      local  gnd, gmap, i, j, ray2, s;
      gnd := [ 1 .. n ];
      SubtractSet( gnd, set );
      gmap := rec(
           );
      j := 1;
      for i  in gnd  do
          gmap.(j) := i;
          j := j + 1;
      od;
      ray2 := EmptyPlist( 2 ^ Size( gnd ) - 1 );
      for s  in Combinations( [ 1 .. Size( gnd ) ] )  do
          if Size( s ) > 0  then
              ray2[set2int( s )] := ray[set2int( RecSetwise( gmap, s ) )];
          fi;
      od;
      return [ ray2, gmap ];
  end;

  OnRay:=function ( ray, n, g )
      local  r2, s;
      r2 := EmptyPlist( Size( ray ) );
      for s  in Combinations( [ 1 .. n ] )  do
          if Size( s ) > 0  then
              r2[set2int( OnSets( s, g ) )] := ray[set2int( s )];
          fi;
      od;
      return r2;
  end;
  IsVamosRay:=function ( ray )
      local  vray, g;
      vray := [ 2, 2, 3, 2, 3, 3, 4, 2, 3, 4, 4, 3, 4, 4, 4 ];
      for g  in SymmetricGroup( 4 )  do
          if vray = OnRay( ray, 4, g )  then
              return [ true, g ];
          fi;
      od;
      return [ false ];
  end;


    HasVamos:=function ( ray, n )
        local  S;
        for S  in Combinations( [ 1 .. n ], n - 4 )  do
            if IsVamosRay( ray_delminor( ray, n, S )[1] )[1]  then
                Display( S );
                return true;
            fi;
        od;
        return false;
    end;

OnEntropySpaceByMat:=function(ray,M)
  return M*ray;
end;

OnEntropySpacePowerSetByMat:=function(rays,M)
  local Mrays,ray;
  Mrays:=[];
  for ray in rays do
    Append(Mrays,[M*ray]);
  od;
  Mrays:=SortedList(Mrays);
  return Mrays;
end;




GenVonNeumannUnbounded:=function(n)
# Returns [A,b] s.t. Ax<=b are the inequalities
# Based on Nicholas Pippenger. The inequalities of quantum information theory. Information Theory, IEEE
# Transactions on, 49(4):773–789, 2003.
local row,vineq,i,j,S,T,itr,k,I,J,t;
  # construct Strong subadditivity inequalities
  # i=I\J
  if n=1 then
    return [[-1],[0]];
  elif n=2 then
    return [ [[-1,-1,1],[1,-1,-1],[-1,1,-1]], [0,0,0]];
  fi;
  vineq:=[];
  for i in [1..n] do
    # J =J\I
    for j in [1..n] do
      if i<j then
        S:=[1..n];
        SubtractSet(S,[i,j]);
        itr:=IteratorOfCombinations(S);
        # Loop over intersction of I and J
        for T in itr do
          row:=ZeroMutable([1..2^n-1]);
          I:=Union(T,[i]);
          J:=Union(T,[j]);
          row[set2int(I)]:=-1;
          row[set2int(J)]:=-1;
          row[set2int(Union(I,J))]:=1;
          if Size(T)>0 then
            row[set2int(T)]:=1;
          fi;
          Append(vineq,[row]);
        od;
      fi;
    od;
  od;
  Display(["nSSA =",Size(vineq)]);
  # construct weak monotonocity inequalities
  for k in [1..n] do
    if k < n then
      t:=k+1;
    else
      t:=1;
    fi;
    S:=[1..n];
    SubtractSet(S,[k,t]);
    itr:=IteratorOfCombinations(S);
    for T in itr do
      I:=[k,t];
      I:=Union(I,T);
      J:=[1..n];
      SubtractSet(J,[t]);
      SubtractSet(J,T);
      row:=ZeroMutable([1..2^n-1]);
      row[set2int(I)]:=-1;
      row[set2int(J)]:=-1;
      SubtractSet(I,[k]);
      row[set2int(I)]:=1;
      SubtractSet(J,[k]);
      if Size(J)>0 then
        row[set2int(J)]:=1;
      fi;
      Append(vineq,[row]);
    od;
  od;
  Display(["nTotal =",Size(vineq)]);
  return [vineq,ZeroMutable([1..Size(vineq)])];
end;


v4rays:=[ [ 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1 ],
  [ 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 0 ],
  [ 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0 ],
  [ 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0 ],
  [ 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0 ],
  [ 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0 ],
  [ 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0 ],
  [ 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1 ],
  [ 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0 ],
  [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0 ],
  [ 1, 1, 2, 1, 2, 2, 1, 0, 1, 1, 2, 1, 2, 2, 1 ],
  [ 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1 ],
  [ 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1 ],
  [ 3, 3, 4, 3, 4, 6, 5, 2, 5, 5, 4, 5, 4, 4, 3 ],
  [ 3, 2, 5, 3, 4, 5, 6, 3, 4, 5, 4, 4, 5, 4, 3 ],
  [ 2, 1, 3, 2, 2, 3, 3, 1, 3, 2, 2, 3, 3, 2, 2 ],
  [ 3, 2, 3, 3, 4, 3, 4, 2, 3, 4, 3, 3, 4, 3, 2 ],
  [ 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1 ],
  [ 2, 1, 3, 1, 3, 2, 2, 1, 3, 2, 2, 2, 2, 3, 1 ],
  [ 1, 2, 3, 2, 3, 2, 3, 1, 2, 3, 2, 3, 2, 3, 2 ],
  [ 2, 3, 5, 3, 5, 4, 6, 3, 5, 4, 4, 4, 4, 5, 3 ],
  [ 2, 3, 3, 3, 3, 4, 4, 2, 4, 3, 3, 3, 3, 4, 2 ],
  [ 3, 3, 4, 3, 6, 4, 5, 2, 5, 5, 4, 5, 4, 4, 3 ],
  [ 3, 3, 4, 3, 4, 4, 5, 2, 5, 5, 4, 5, 4, 6, 3 ],
  [ 3, 3, 4, 3, 4, 4, 5, 2, 5, 5, 4, 5, 6, 4, 3 ],
  [ 3, 3, 6, 3, 4, 4, 5, 2, 5, 5, 4, 5, 4, 4, 3 ],
  [ 3, 3, 4, 3, 4, 4, 5, 2, 5, 5, 6, 5, 4, 4, 3 ],
  [ 3, 3, 4, 3, 4, 4, 5, 3, 6, 4, 5, 4, 5, 5, 2 ],
  [ 1, 0, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1 ],
  [ 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 3, 3, 3, 3, 1 ],
  [ 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 2, 3, 2, 2, 1 ],
  [ 1, 1, 2, 0, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1 ],
  [ 2, 3, 3, 2, 4, 3, 3, 2, 4, 3, 3, 4, 4, 3, 3 ],
  [ 2, 3, 5, 3, 5, 4, 4, 3, 5, 4, 4, 6, 4, 5, 3 ],
  [ 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 ],
  [ 2, 3, 5, 3, 5, 4, 4, 3, 5, 4, 4, 4, 6, 5, 3 ],
  [ 2, 2, 4, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 2 ],
  [ 1, 1, 2, 2, 3, 3, 2, 2, 3, 3, 2, 2, 3, 3, 2 ],
  [ 3, 2, 5, 3, 4, 5, 4, 3, 6, 5, 4, 4, 5, 4, 3 ],
  [ 2, 2, 4, 3, 3, 3, 3, 2, 4, 4, 4, 3, 3, 3, 3 ],
  [ 2, 3, 5, 3, 5, 4, 4, 3, 5, 6, 4, 4, 4, 5, 3 ],
  [ 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1 ],
  [ 1, 2, 3, 1, 2, 3, 2, 2, 3, 2, 3, 3, 2, 3, 2 ],
  [ 3, 3, 4, 2, 5, 5, 4, 3, 6, 4, 5, 5, 4, 4, 3 ],
  [ 3, 3, 4, 2, 5, 5, 4, 3, 4, 4, 5, 5, 4, 6, 3 ],
  [ 2, 3, 5, 3, 5, 4, 4, 3, 5, 4, 6, 4, 4, 5, 3 ],
  [ 2, 3, 3, 2, 4, 3, 3, 3, 3, 4, 4, 3, 3, 4, 2 ],
  [ 2, 2, 2, 1, 3, 3, 3, 1, 3, 3, 3, 2, 2, 2, 2 ],
  [ 3, 3, 4, 2, 3, 3, 4, 2, 3, 3, 4, 4, 3, 3, 2 ],
  [ 3, 3, 4, 2, 5, 5, 6, 3, 4, 4, 5, 5, 4, 4, 3 ],
  [ 3, 3, 4, 3, 6, 4, 5, 3, 4, 4, 5, 4, 5, 5, 2 ],
  [ 2, 2, 2, 1, 3, 3, 3, 2, 2, 2, 2, 3, 3, 3, 1 ],
  [ 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 3, 3, 2, 2, 1 ],
  [ 3, 3, 4, 3, 4, 6, 5, 3, 4, 4, 5, 4, 5, 5, 2 ],
  [ 0, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1 ],
  [ 3, 3, 4, 3, 4, 4, 5, 3, 4, 6, 5, 4, 5, 5, 2 ],
  [ 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 6, 5, 5, 2 ],
  [ 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 2 ],
  [ 1, 2, 3, 1, 2, 3, 2, 1, 2, 3, 2, 2, 3, 2, 1 ],
  [ 2, 1, 3, 2, 2, 3, 3, 2, 2, 3, 3, 2, 2, 3, 1 ],
  [ 3, 3, 6, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 2 ],
  [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 ],
  [ 3, 2, 3, 2, 3, 4, 3, 2, 3, 4, 3, 4, 3, 4, 3 ],
  [ 2, 2, 4, 2, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3 ],
  [ 2, 3, 5, 3, 5, 6, 4, 3, 5, 4, 4, 4, 4, 5, 3 ],
  [ 3, 2, 5, 3, 6, 5, 4, 3, 4, 5, 4, 4, 5, 4, 3 ],
  [ 3, 2, 5, 3, 4, 5, 4, 3, 4, 5, 4, 4, 5, 6, 3 ],
  [ 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 ],
  [ 3, 2, 5, 3, 4, 5, 4, 3, 4, 5, 4, 6, 5, 4, 3 ],
  [ 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 ],
  [ 3, 3, 4, 2, 5, 5, 4, 3, 4, 6, 5, 5, 4, 4, 3 ],
  [ 3, 3, 6, 2, 5, 5, 4, 3, 4, 4, 5, 5, 4, 4, 3 ],
  [ 3, 3, 4, 2, 5, 5, 4, 3, 4, 4, 5, 5, 6, 4, 3 ],
  [ 2, 1, 3, 1, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 2 ],
  [ 3, 2, 5, 3, 4, 5, 4, 3, 4, 5, 6, 4, 5, 4, 3 ],
  [ 3, 2, 3, 2, 3, 4, 3, 3, 4, 3, 4, 3, 4, 3, 2 ] ];

v3rays:=[ [ 0, 1, 1, 0, 0, 1, 1 ],
  [ 0, 1, 1, 1, 1, 0, 0 ],
  [ 1, 0, 1, 1, 0, 1, 0 ],
  [ 1, 1, 0, 0, 1, 1, 0 ],
  [ 1, 0, 1, 0, 1, 0, 1 ],
  [ 1, 1, 2, 1, 2, 2, 1 ],
  [ 0, 0, 0, 1, 1, 1, 1 ],
  [ 1, 1, 1, 1, 1, 1, 1 ] ];

v2rays:=[[1,0,1],[1,1,0],[0,1,1]];

V2:=Group([ (2,3),
 (1,2),
 (1,3)]);

V3:=Group([(5,7),
(4,5),
(3,4),
(2,3),
(1,2),
(4,7),
(2,4)]);

V4:=Group([ (4,9)(5,7)(8,12)(14,26)(18,52)(19,53)(20,48)(21,50)(22,49)(24,27)(28,57)(32,55)(34,44)(35,70)(36,73)(37,76)(38,74)(39,69)(40,63)(41,71)(45,46)(54,61)(65,72)(67,75),
 (1,12)(3,9)(6,7)(15,50)(16,48)(17,49)(23,26)(25,27)(29,32)(33,40)(34,41)(36,46)(37,47)(38,43)(39,44)(45,67)(51,61)(52,60)(53,59)(56,57)(66,72)(68,70)(69,71)(73,75),
 (1,42)(4,7)(5,9)(11,29)(13,68)(14,69)(15,25)(20,38)(21,36)(22,37)(23,66)(24,67)(26,39)(27,75)(28,61)(30,60)(31,59)(33,64)(34,65)(44,72)(48,74)(49,76)(50,73)(54,57),
 (1,3)(2,11)(4,8)(9,12)(10,13)(14,54)(16,60)(18,20)(23,51)(24,28)(25,56)(26,61)(27,57)(31,58)(33,47)(34,46)(36,41)(37,40)(39,67)(44,45)(48,52)(63,76)(69,75)(71,73),
 (2,29)(3,42)(5,12)(7,8)(10,68)(14,27)(15,56)(16,30)(18,38)(21,41)(22,40)(24,26)(28,39)(45,72)(46,65)(47,64)(49,63)(50,71)(51,66)(52,74)(54,75)(57,69)(58,59)(61,67),
 (3,7)(6,9)(8,42)(11,55)(13,35)(14,65)(15,67)(16,38)(17,37)(18,30)(19,31)(21,24)(23,34)(25,36)(26,41)(27,46)(43,48)(45,50)(47,49)(51,57)(56,61)(63,64)(66,69)(71,72)]);

VM2gens:= [ [ [ 0, 0, 1 ], [ 0, 1, 0 ], [ 1, 0, 0 ] ], [ [ 1, 0, 0 ], [ 0, 0, 1 ], [ 0, 1, 0 ] ], [ [ 0, 1, 0 ], [ 1, 0, 0 ], [ 0, 0, 1 ] ] ];

VM3gens:= [ [ [ 1/2, 0, -1/2, 1/2, 0, 1/2, 0 ],
      [ 0, 1, 0, 0, 0, 0, 0 ],
      [ -1/2, 0, 1/2, 1/2, 0, 1/2, 0 ],
      [ 1/2, 0, 1/2, 1/2, 0, -1/2, 0 ],
      [ 0, 0, 0, 0, 1, 0, 0 ],
      [ 1/2, 0, 1/2, -1/2, 0, 1/2, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1 ] ],
  [ [ 1, 0, 0, 0, 0, 0, 0 ],
      [ 0, 1/2, 1/2, 0, 0, -1/2, 1/2 ],
      [ 0, 1/2, 1/2, 0, 0, 1/2, -1/2 ],
      [ 0, 0, 0, 1, 0, 0, 0 ],
      [ 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, -1/2, 1/2, 0, 0, 1/2, 1/2 ],
      [ 0, 1/2, -1/2, 0, 0, 1/2, 1/2 ] ],
  [ [ 1, 0, 0, 0, 0, 0, 0 ],
      [ 0, 1/2, 1/2, 1/2, -1/2, 0, 0 ],
      [ 0, 1/2, 1/2, -1/2, 1/2, 0, 0 ],
      [ 0, 1/2, -1/2, 1/2, 1/2, 0, 0 ],
      [ 0, -1/2, 1/2, 1/2, 1/2, 0, 0 ],
      [ 0, 0, 0, 0, 0, 1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1 ] ],
  [ [ 1/2, 1/2, 0, 0, 1/2, -1/2, 0 ],
      [ 1/2, 1/2, 0, 0, -1/2, 1/2, 0 ],
      [ 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 1, 0, 0, 0 ],
      [ 1/2, -1/2, 0, 0, 1/2, 1/2, 0 ],
      [ -1/2, 1/2, 0, 0, 1/2, 1/2, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1 ] ],
  [ [ 1, 0, 0, 0, 0, 0, 0 ],
      [ 0, 1, 0, 0, 0, 0, 0 ],
      [ 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 1/2, -1/2, 1/2, 1/2 ],
      [ 0, 0, 0, -1/2, 1/2, 1/2, 1/2 ],
      [ 0, 0, 0, 1/2, 1/2, 1/2, -1/2 ],
      [ 0, 0, 0, 1/2, 1/2, -1/2, 1/2 ] ],
  [ [ 1/2, -1/2, 0, 1/2, 0, 0, 1/2 ],
      [ -1/2, 1/2, 0, 1/2, 0, 0, 1/2 ],
      [ 0, 0, 1, 0, 0, 0, 0 ],
      [ 1/2, 1/2, 0, 1/2, 0, 0, -1/2 ],
      [ 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 1, 0 ],
      [ 1/2, 1/2, 0, -1/2, 0, 0, 1/2 ] ],
  [ [ 1/2, 0, 1/2, 1/2, 0, -1/2, 0 ],
      [ 0, 1, 0, 0, 0, 0, 0 ],
      [ 1/2, 0, 1/2, -1/2, 0, 1/2, 0 ],
      [ 1/2, 0, -1/2, 1/2, 0, 1/2, 0 ],
      [ 0, 0, 0, 0, 1, 0, 0 ],
      [ -1/2, 0, 1/2, 1/2, 0, 1/2, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1 ] ] ];

VM4gens:=[ [ [ 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 ] ],
  [ [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 ] ],
  [ [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 ] ],
  [ [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0 ] ],
  [ [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 ],
      [ 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ] ],
  [ [ 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 ],
      [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 ] ] ];

siftfuncs:=function(str)
local funclist,i,j,funcpos;
funclist:=[];
funcpos:=[];
for i in [1..Size(str)] do
if not i+22> Size(str) then
  if str{[i..i+22]}="\nDeclareGlobalFunction(" then
    # get function name
    for j in [i+24..Size(str)] do
      if str[j]='\n' then
        break;
      fi;
    od;
    Append(funclist,[str{[i+24..j-4]}]);
    Append(funcpos,[j+1]);
  fi;
fi;
od;
return [funclist,funcpos];
end;

siftex:=function(str)
local funclist,i,j,k,funcex;
funclist:=[];
funcex:=[];
for i in [1..Size(str)] do
if not i+3> Size(str) then
  if str{[i..i+3]}="#!##" then
    # get function name
    for j in [i+4..Size(str)] do
      if str[j]='\n' then
        break;
      fi;
    od;
    Append(funclist,[str{[i+4..j-1]}]);
    for k in [j+1..Size(str)] do
      if not k+ 14>Size(str) then
      if str{[k..k+14]}="#! @EndExample\n" then
        Append(funcex,[str{[j+1..k+14]}]);
        break;
      fi;
      fi;
    od;
  fi;
fi;
od;
return [funclist,funcex];
end;

mergex:=function(strgd,funcsdata,exdata)
local offset,f,i,str1,str2,str3,str,chunklist;
  offset:=1;
  str:=ShallowCopy(strgd);
  chunklist:=[];
  for f in funcsdata[1] do # loop over all functions
    if f in exdata[1] then # if f has an example
    i:=funcsdata[2][Position(funcsdata[1],f)]; # break str here
    str1:=str{[offset..i-1]};
    offset:=i;
    Append(chunklist,[str1]);
    Append(chunklist,[exdata[2][Position(exdata[1],f)]]);
    fi;
  od;
  Append(chunklist,[str{[offset..Size(str)]}]);
  return Concatenation(chunklist);
end;


unmergex:=function(strgd)
local funcchunks,exchunks,offset,i,j;
funcchunks:=[];
exchunks:=[];
offset:=1;
i:=1;
while not i>=Size(strgd) do
if not i+16 > Size(strgd) then
  if strgd{[i..i+16]}="#! @BeginExample\n" then
    Append(funcchunks,[strgd{[offset..i-1]}]);
    for j in [i+17..Size(strgd)] do
    if strgd{[j..j+14]}="#! @EndExample\n" then
      Append(exchunks,[strgd{[i..j+14]}]);
      offset:=j+15;
      i:=j+15;
      break;
    fi;
    od;
  else
    i:=i+1;
  fi;
else
  Append(funcchunks,[strgd{[offset..Size(strgd)]}]); # appendleftover stuff to funcchunks
  break;
fi;
od;
return [Concatenation(funcchunks),Concatenation(exchunks)];
end;

buildman:=function(path)
local ip,fstr,exstr,frlist,exrlist,mstr,op;
ip:=InputTextFile(Concatenation(path,"gap/itcp.gd"));
fstr:=ReadAll(ip);;
CloseStream(ip);
ip:=InputTextFile(Concatenation(path,"doc/examples.txt"));
exstr:=ReadAll(ip);;
CloseStream(ip);
frlist:=siftfuncs(fstr);;
exrlist:=siftex(exstr);;
mstr:=mergex(fstr,frlist,exrlist);
op:=OutputTextFile(Concatenation(path,"gap/itcp.gd"),false);
WriteAll(op,mstr);
CloseStream(op);
AutoDoc("itcp":autodoc:=true);
op:=OutputTextFile(Concatenation(path,"gap/itcp.gd"),false);
WriteAll(op,fstr);
CloseStream(op);
end;

#ip:=InputTextFile("/home/jayant/Documents/itap_light.gd");
#fstr:=ReadAll(ip);;
#CloseStream(ip);
#ip:=InputTextFile("/home/jayant/Documents/examples.txt");
#exstr:=ReadAll(ip);;
#CloseStream(ip);
#frlist:=siftfuncs(fstr);;
#exrlist:=siftex(exstr);;
#mstr:=mergex(fstr,frlist,exrlist);

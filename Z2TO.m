(* ::Package:: *)

(* ::Input:: *)
(*ClearAll["Global`*"]*)


(* ::Section:: *)
(*Anomaly Indicator*)


IndicatorZ2T[g_List,Action_List, SF_List,ActionGenerate_, SFGenerate_ ]:=Module[{flag,s,Ind},
flag = ActionGenerate[g,Action];
Ind=1;
If[flag==0,
s=SFGenerate[g,g,Action,SF];
Ind=Mod[s[[1]]*s[[2]],2];
];
Ind];

IndicatorZ2TZ2T[g1_List,g2_List,Action_List, SF_List,ActionGenerate_, SFGenerate_]:=Module[{flag1,flag2,s,t,st,Ind},
flag1= ActionGenerate[g1,Action];
flag2= ActionGenerate[g2,Action];
Ind=1;
If[flag1==0&&flag2==0,
s=SFGenerate[g1,g1,Action,SF];
t=SFGenerate[g2,g2,Action,SF];
st=SFGenerate[g1,g2,Action,SF]+SFGenerate[g2,g1,Action,SF];
Ind=Mod[s[[1]]*t[[2]]+s[[2]]*t[[1]]+st[[1]]*st[[2]],2];];
If[flag1==1&&flag2==0,
t=SFGenerate[g2,g2,Action,SF];
Ind=Mod[t[[1]],2];];
If[flag1==0&&flag2==1,
t=SFGenerate[g1,g1,Action,SF];
Ind=Mod[t[[1]],2];];
If[flag1==1&&flag2==1,
st=SFGenerate[g1,g1,Action,SF]+SFGenerate[g2,g2,Action,SF]+SFGenerate[g1,g2,Action,SF]+SFGenerate[g2,g1,Action,SF];
Ind=Mod[st[[1]],2];];
Ind];

IndicatorSO3[Action_List, SF_List,SFGenerate_]:=Module[{s,Ind},
s=SFGenerate[{0,0,0,0,0,1},{0,0,0,0,0,1},Action,SF];
Ind=Mod[s[[1]]*s[[2]],2];
Ind];

IndicatorZ2[g_List,Action_List, SF_List,ActionGenerate_, SFGenerate_]:=Module[{flag,s,st,Ind},
flag=ActionGenerate[g,Action];
Ind =1;
If[flag==0,
st=SFGenerate[{0,0,0,0,0,1},{0,0,0,0,0,1},Action,SF];
s=SFGenerate[g,g,Action,SF];
Ind=Mod[s[[1]]*st[[2]]+s[[2]]*st[[1]],2];
];
Ind]


(* ::Chapter:: *)
(*Symmetry: p6m*)


p6mBxy[g1_List, g2_List]:=Which[Mod[g1[[3]],6]==0&&Mod[g1[[4]],2]==0, g1[[2]]*g2[[1]],
Mod[g1[[3]],6]==1&&Mod[g1[[4]],2]==0,g2[[1]]*(g2[[1]]-1)/2-g2[[2]]*g2[[1]]+g1[[2]]*(g2[[1]]-g2[[2]]),
Mod[g1[[3]],6]==2&&Mod[g1[[4]],2]==0,g2[[2]]*(g2[[2]]+1)/2-g2[[1]]-g2[[2]]*(g1[[2]]+g2[[1]]),
Mod[g1[[3]],6]==3&&Mod[g1[[4]],2]==0, -g2[[1]]+g2[[2]]-g1[[2]]*g2[[1]],
Mod[g1[[3]],6]==4&&Mod[g1[[4]],2]==0,  g2[[1]]*(g2[[1]]-1)/2+g2[[2]]-g2[[1]]*g1[[2]]+g2[[2]]*(g1[[2]]-g2[[1]]),
Mod[g1[[3]],6]==5&&Mod[g1[[4]],2]==0, g2[[2]]*(g2[[2]]+1)/2+g2[[2]]*(g1[[2]]-g2[[1]]),
Mod[g1[[3]],6]==0&&Mod[g1[[4]],2]==1, (g1[[2]]+g2[[1]])*g2[[2]],
Mod[g1[[3]],6]==1&&Mod[g1[[4]],2]==1, g2[[2]]*(g2[[2]]-1)/2+g1[[2]]*(-g2[[1]]+g2[[2]]),
Mod[g1[[3]],6]==2&&Mod[g1[[4]],2]==1, g2[[1]]*(g2[[1]]+1)/2-g2[[2]]-g2[[1]]*g1[[2]],
Mod[g1[[3]],6]==3&&Mod[g1[[4]],2]==1, g2[[1]]-g2[[2]]-(g1[[2]]-g2[[1]])*g2[[2]],
Mod[g1[[3]],6]==4&&Mod[g1[[4]],2]==1, g2[[2]]*(g2[[2]]-1)/2+g2[[1]]+g1[[2]]*(g2[[1]]-g2[[2]]),
Mod[g1[[3]],6]==5&&Mod[g1[[4]],2]==1,g2[[1]]*(g2[[1]]+1)/2+g2[[1]]*g1[[2]]];


(* ::Section:: *)
(*SO(3)*Z2T*)


p6mO3ActionGenerate[g_List,Action_List]:=Mod[g[[3]]*Action[[1]]+g[[4]]*Action[[2]]+g[[5]]*Action[[3]],2];

p6mO3SFGenerate[g1_List,g2_List,Action_List,SF_List]:=Mod[
Which[Action[[1]]==0&&Action[[2]]==0&&Action[[3]]==0,
p6mBxy[g1,g2]*{SF[[1]][[1]],SF[[2]][[1]]}+g1[[3]]*g2[[3]]*{SF[[1]][[2]],SF[[2]][[2]]}+g1[[3]]*g2[[4]]*{SF[[1]][[3]],SF[[2]][[3]]}+g1[[4]]*g2[[4]]*{SF[[1]][[4]],SF[[2]][[4]]}+g1[[3]]*g2[[5]]*{SF[[1]][[5]],SF[[2]][[5]]}+g1[[4]]*g2[[5]]*{SF[[1]][[6]],SF[[2]][[6]]}+g1[[5]]*g2[[5]]*{SF[[1]][[7]],SF[[2]][[7]]}+g1[[6]]*g2[[6]]*{SF[[1]][[8]],SF[[2]][[8]]},
Action[[3]]==1,
p6mBxy[g1,g2]*{SF[[1]],SF[[1]]}+g1[[3]]*g2[[3]]*{SF[[2]],SF[[2]]}+g1[[3]]*g2[[4]]*{SF[[3]],SF[[3]]}+g1[[4]]*g2[[4]]*{SF[[4]],SF[[4]]}+g1[[6]]*g2[[6]]*{SF[[5]],SF[[5]]},
Action[[2]]==1&&Action[[3]]==0,
p6mBxy[g1,g2]*{SF[[1]],SF[[1]]}+g1[[3]]*g2[[3]]*{SF[[2]],SF[[2]]}+g1[[3]]*g2[[5]]*{SF[[3]],SF[[3]]}+g1[[5]]*g2[[5]]*{SF[[4]],SF[[4]]}+g1[[6]]*g2[[6]]*{SF[[5]],SF[[5]]},
Action[[1]]==1&&Action[[2]]==0&&Action[[3]]==0,
p6mBxy[g1,g2]*{SF[[1]],SF[[1]]}+g1[[4]]*g2[[4]]*{SF[[2]],SF[[2]]}+g1[[4]]*g2[[5]]*{SF[[3]],SF[[3]]}+g1[[5]]*g2[[5]]*{SF[[4]],SF[[4]]}+g1[[6]]*g2[[6]]*{SF[[5]],SF[[5]]}]
,2];


p6mO3Multiply[Action_List, SF_List]:={IndicatorZ2T[{0,0,0,0,1,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],IndicatorZ2T[{0,0,0,1,0,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2T[{0,0,3,0,1,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2T[{0,0,3,1,0,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,0,0,1,0},{0,0,3,0,1,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,0,0,1,0},{0,0,0,1,0,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,0,1,0,0},{0,0,3,0,1,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,3,0,1,0},{0,0,3,1,0,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,0,1,0,0},{0,0,3,1,0,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2T[{1,1,3,0,1,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,0,1,0,0},{1,1,3,0,1,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,0,0,1,0},{1,1,3,0,1,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2TZ2T[{0,0,0,1,0,0},{1,1,3,1,0,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2T[{0,0,0,0,1,1},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2T[{0,0,0,1,0,1},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2T[{0,0,3,0,1,1},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2T[{0,0,3,1,0,1},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2T[{1,1,3,0,1,1},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorSO3[Action, SF, p6mO3SFGenerate],
IndicatorZ2[{0,0,3,0,0,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate],
IndicatorZ2[{0,0,0,1,1,0},Action, SF, p6mO3ActionGenerate, p6mO3SFGenerate]}


p6mO3Anomaly0=ConstantArray[0,21];
p6mO3Anomalya=ConstantArray[0,21];p6mO3Anomalya[[3]]=1;p6mO3Anomalya[[5]]=1;p6mO3Anomalya[[20]]=1;
p6mO3Anomalyc=ConstantArray[0,21];p6mO3Anomalyc[[10]]=1;p6mO3Anomalyc[[12]]=1;
p6mO3Anomalyac=Mod[p6mO3Anomalya+p6mO3Anomalyc,2];


p6mO3Generate[Action_,homotopylist_]:=Module[{result,ActionList, Anomaly, matchinganomaly, i, j, SFCe, SFCm},
result={};Do[AppendTo[result, {}], {i, 1, Length[homotopylist]}];
matchinganomaly = {};
For[i=1,i<=Length[homotopylist],i++, 
If[homotopylist[[i]]=="0", AppendTo[matchinganomaly, p6mO3Anomaly0];];
If[homotopylist[[i]]=="a", AppendTo[matchinganomaly, p6mO3Anomalya];];
If[homotopylist[[i]]=="c", AppendTo[matchinganomaly, p6mO3Anomalyc];];
If[homotopylist[[i]]=="a+c", AppendTo[matchinganomaly, p6mO3Anomalyac];];];
ActionList=PadLeft[IntegerDigits[Action,2],3];
If[Action==0,
For[i=0,i<2^8,i++,
	For[j=0,j<=i,j++,
SFCe=PadLeft[IntegerDigits[i,2],8];
SFCm=PadLeft[IntegerDigits[j,2],8];
Anomaly=p6mO3Multiply[ActionList,{SFCe,SFCm}];
Do[If[Anomaly==matchinganomaly[[i]], AppendTo[result[[i]], Join[SFCe, SFCm]];Break[]], {i, 1, Length[homotopylist]}];
]],
For[i=0,i<2^5,i++,
SFCe=PadLeft[IntegerDigits[i,2],5];
Anomaly=p6mO3Multiply[ActionList,SFCe];
Do[If[Anomaly==matchinganomaly[[i]], AppendTo[result[[i]], SFCe];Break[]], {i, 1, Length[homotopylist]}];];
];
result]


(* ::Input:: *)
(*result1=p6mO3Generate[0,{"0", "a", "c", "a+c"}];*)


(* ::Input:: *)
(*(*Number of symmetry-enriched Z4 topological quantum spin liquids in each lattice homotopy class, with anyon permutation pattern 1*)*)
(*Length[result1[[1]]](*class 0*)*)
(*Length[result1[[2]]](*class a*)*)
(*Length[result1[[3]]](*class c*)*)
(*Length[result1[[4]]](*class a+c*)*)


(* ::Subsubsection::Closed:: *)
(*No Anyon Permutation*)


(* ::Input:: *)
(*zero0=p6mCheckLSM[zero,0,0,0];*)
(*a0=p6mCheckLSM[a,0,0,0];*)
(*c0=p6mCheckLSM[c,0,0,0];*)
(*ac0=p6mCheckLSM[ac,0,0,0];*)
(**)
(*Length[zero0]*)
(*Length[a0]*)
(*Length[c0]*)
(*Length[ac0]*)


(* ::Subsubsection::Closed:: *)
(*With Anyon Permutation*)


(* ::Input:: *)
(*Do[If[i1!=0||i2!=0||i3!=0,Print[p6mCheckLSM[zero,i1,i2,i3]];],{i1,0,1},{i2,0,1},{i3,0,1}]*)


(* ::Input:: *)
(*Do[If[i1!=0||i2!=0||i3!=0,Print[p6mCheckLSM[a,i1,i2,i3]];],{i1,0,1},{i2,0,1},{i3,0,1}]*)


(* ::Input:: *)
(*Do[If[i1!=0||i2!=0||i3!=0,Print[p6mCheckLSM[c,i1,i2,i3]];],{i1,0,1},{i2,0,1},{i3,0,1}]*)


(* ::Input:: *)
(*Do[If[i1!=0||i2!=0||i3!=0,Print[p6mCheckLSM[ac,i1,i2,i3]];],{i1,0,1},{i2,0,1},{i3,0,1}]*)


(* ::Section::Closed:: *)
(*Z2T*)


(* ::Input:: *)
(*zero=ConstantArray[0,13];*)
(*a=ConstantArray[0,13];a[[3]]=1;a[[5]]=1;*)
(*c=ConstantArray[0,13];c[[10]]=1;c[[12]]=1;*)
(*ac=Mod[a+c,2];*)


(* ::Input:: *)
(*p6mBxy[g1_List, g2_List]:=Which[Mod[g1[[3]],6]==0&&Mod[g1[[4]],2]==0, g1[[2]]*g2[[1]],*)
(*Mod[g1[[3]],6]==1&&Mod[g1[[4]],2]==0,g2[[1]]*(g2[[1]]-1)/2-g2[[2]]*g2[[1]]+g1[[2]]*(g2[[1]]-g2[[2]]),*)
(*Mod[g1[[3]],6]==2&&Mod[g1[[4]],2]==0,g2[[2]]*(g2[[2]]+1)/2-g2[[1]]-g2[[2]]*(g1[[2]]+g2[[1]]),*)
(*Mod[g1[[3]],6]==3&&Mod[g1[[4]],2]==0, -g2[[1]]+g2[[2]]-g1[[2]]*g2[[1]],*)
(*Mod[g1[[3]],6]==4&&Mod[g1[[4]],2]==0,  g2[[1]]*(g2[[1]]-1)/2+g2[[2]]-g2[[1]]*g1[[2]]+g2[[2]]*(g1[[2]]-g2[[1]]),*)
(*Mod[g1[[3]],6]==5&&Mod[g1[[4]],2]==0, g2[[2]]*(g2[[2]]+1)/2+g2[[2]]*(g1[[2]]-g2[[1]]),*)
(*Mod[g1[[3]],6]==0&&Mod[g1[[4]],2]==1, (g1[[2]]+g2[[1]])*g2[[2]],*)
(*Mod[g1[[3]],6]==1&&Mod[g1[[4]],2]==1, g2[[2]]*(g2[[2]]-1)/2+g1[[2]]*(-g2[[1]]+g2[[2]]),*)
(*Mod[g1[[3]],6]==2&&Mod[g1[[4]],2]==1, g2[[1]]*(g2[[1]]+1)/2-g2[[2]]-g2[[1]]*g1[[2]],*)
(*Mod[g1[[3]],6]==3&&Mod[g1[[4]],2]==1, g2[[1]]-g2[[2]]-(g1[[2]]-g2[[1]])*g2[[2]],*)
(*Mod[g1[[3]],6]==4&&Mod[g1[[4]],2]==1, g2[[2]]*(g2[[2]]-1)/2+g2[[1]]+g1[[2]]*(g2[[1]]-g2[[2]]),*)
(*Mod[g1[[3]],6]==5&&Mod[g1[[4]],2]==1,g2[[1]]*(g2[[1]]+1)/2+g2[[1]]*g1[[2]]];*)


(* ::Input:: *)
(*p6mSFClass[g1_List,g2_List,SF_List,actionC_,actionM_, actionT_]:=Mod[*)
(*Which[actionC==0&&actionM==0&&actionT==0,*)
(*p6mBxy[g1,g2]*{SF[[1]][[1]],SF[[2]][[1]]}+g1[[3]]*g2[[3]]*{SF[[1]][[2]],SF[[2]][[2]]}+g1[[3]]*g2[[4]]*{SF[[1]][[3]],SF[[2]][[3]]}+g1[[4]]*g2[[4]]*{SF[[1]][[4]],SF[[2]][[4]]}+g1[[3]]*g2[[5]]*{SF[[1]][[5]],SF[[2]][[5]]}+g1[[4]]*g2[[5]]*{SF[[1]][[6]],SF[[2]][[6]]}+g1[[5]]*g2[[5]]*{SF[[1]][[7]],SF[[2]][[7]]},*)
(*actionT==1,*)
(*p6mBxy[g1,g2]*{SF[[1]],SF[[1]]}+g1[[3]]*g2[[3]]*{SF[[2]],SF[[2]]}+g1[[3]]*g2[[4]]*{SF[[3]],SF[[3]]}+g1[[4]]*g2[[4]]*{SF[[4]],SF[[4]]},*)
(*actionM==1&&actionT==0,*)
(*p6mBxy[g1,g2]*{SF[[1]],SF[[1]]}+g1[[3]]*g2[[3]]*{SF[[2]],SF[[2]]}+g1[[3]]*g2[[5]]*{SF[[3]],SF[[3]]}+g1[[5]]*g2[[5]]*{SF[[4]],SF[[4]]},*)
(*actionC==1&&actionM==0&&actionT==0,*)
(*p6mBxy[g1,g2]*{SF[[1]],SF[[1]]}+g1[[4]]*g2[[4]]*{SF[[2]],SF[[2]]}+g1[[4]]*g2[[5]]*{SF[[3]],SF[[3]]}+g1[[5]]*g2[[5]]*{SF[[4]],SF[[4]]}]*)
(*,2];*)


(* ::Input:: *)
(*p6mCheckIndZ2T[g_List,SF_List,actionC_,actionM_,actionT_]:=Module[{flag,s,Ind},*)
(*flag = Mod[g[[3]]*actionC+g[[4]]*actionM+g[[5]]*actionT,2];*)
(*Ind=1;*)
(*If[flag==0,*)
(*s=p6mSFClass[g,g,SF,actionC,actionM,actionT];*)
(*Ind=IndicatorZ2TS1[s[[1]],s[[2]]];*)
(*];*)
(*Ind];*)
(**)
(*p6mCheckIndZ2TZ2T[g1_List,g2_List,SF_List,actionC_,actionM_,actionT_]:=Module[{flag1,flag2,s,t,st,Ind},*)
(*flag1= Mod[g1[[3]]*actionC+g1[[4]]*actionM+g1[[5]]*actionT,2];*)
(*flag2= Mod[g2[[3]]*actionC+g2[[4]]*actionM+g2[[5]]*actionT,2];*)
(*Ind=1;*)
(*If[flag1==0&&flag2==0,*)
(*s=p6mSFClass[g1,g1,SF,actionC,actionM,actionT];*)
(*t=p6mSFClass[g2,g2,SF,actionC,actionM,actionT];*)
(*st=Mod[p6mSFClass[g1,g2,SF,actionC,actionM,actionT]+p6mSFClass[g2,g1,SF,actionC,actionM,actionT],2];*)
(*Ind=IndicatorZ2TZ2TS1[s[[1]],s[[2]],t[[1]],t[[2]],st[[1]],st[[2]]];];*)
(*If[flag1==1&&flag2==0,*)
(*t=p6mSFClass[g2,g2,SF,actionC,actionM,actionT];*)
(*Ind=IndicatorZ2TZ2TS2[t[[1]]];];*)
(*If[flag1==0&&flag2==1,*)
(*t=p6mSFClass[g1,g1,SF,actionC,actionM,actionT];*)
(*Ind=IndicatorZ2TZ2TS2[t[[1]]];];*)
(*If[flag1==1&&flag2==1,*)
(*st=Mod[p6mSFClass[g1,g1,SF,actionC,actionM,actionT]+p6mSFClass[g2,g2,SF,actionC,actionM,actionT]+p6mSFClass[g1,g2,SF,actionC,actionM,actionT]+p6mSFClass[g2,g1,SF,actionC,actionM,actionT],2];*)
(*Ind=IndicatorZ2TZ2TS2[st[[1]]];];*)
(*Ind];*)


(* ::Input:: *)
(*p6mCheckLSM[LSMList_List,actionC_,actionM_,actionT_]:=Module[{m,Dim,SFList,PossibilityList},*)
(*PossibilityList = {};*)
(**)
(*Dim=If[actionC==0&&actionM==0&&actionT==0,14,4];*)
(**)
(*For[m=0,m<2^Dim,m++,*)
(*SFList=PadLeft[IntegerDigits[m,2],Dim];*)
(**)
(*If[actionC==0&&actionM==0&&actionT==0,If[Quotient[m,2^7]<Mod[m,2^7],Continue[];];SFList={SFList[[1;;7]],SFList[[8;;14]]}];*)
(**)
(*If[p6mCheckIndZ2T[{0,0,0,0,1,0},SFList,actionC,actionM,actionT]!=(-1)^LSMList[[1]],Continue[];];*)
(*If[p6mCheckIndZ2T[{0,0,0,1,0,0},SFList,actionC,actionM,actionT]!=(-1)^LSMList[[2]],Continue[];];*)
(*If[p6mCheckIndZ2T[{0,0,3,0,1,0},SFList,actionC,actionM,actionT]!=(-1)^LSMList[[3]],Continue[];];*)
(*If[p6mCheckIndZ2T[{0,0,3,1,0,0},SFList,actionC,actionM,actionT]!=(-1)^LSMList[[4]],Continue[];];*)
(**)
(*If[p6mCheckIndZ2TZ2T[{0,0,0,0,1,0},{0,0,3,0,1,0},SFList,actionC,actionM,actionT]!=(-1)^LSMList[[5]],Continue[];];*)
(*If[p6mCheckIndZ2TZ2T[{0,0,0,0,1,0},{0,0,0,1,0,0},SFList,actionC,actionM,actionT]!=(-1)^LSMList[[6]],Continue[];];*)
(*If[p6mCheckIndZ2TZ2T[{0,0,0,1,0,0},{0,0,3,0,1,0},SFList,actionC,actionM,actionT]!=(-1)^LSMList[[7]],Continue[];];*)
(*If[p6mCheckIndZ2TZ2T[{0,0,3,0,1,0},{0,0,3,1,0,0},SFList,actionC,actionM,actionT]!=(-1)^LSMList[[8]],Continue[];];*)
(*If[p6mCheckIndZ2TZ2T[{0,0,0,1,0,0},{0,0,3,1,0,0},SFList,actionC,actionM,actionT]!=(-1)^LSMList[[9]],Continue[];];*)
(**)
(*If[p6mCheckIndZ2T[{1,1,3,0,1,0},SFList,actionC,actionM,actionT]!=(-1)^LSMList[[10]],Continue[];];*)
(*If[p6mCheckIndZ2TZ2T[{0,0,0,1,0,0},{1,1,3,0,1,0},SFList,actionC,actionM,actionT]!=(-1)^LSMList[[11]],Continue[];];*)
(*If[p6mCheckIndZ2TZ2T[{0,0,0,0,1,0},{1,1,3,0,1,0},SFList,actionC,actionM,actionT]!=(-1)^LSMList[[12]],Continue[];];*)
(*If[p6mCheckIndZ2TZ2T[{0,0,0,1,0,0},{1,1,3,1,0,0},SFList,actionC,actionM,actionT]!=(-1)^LSMList[[13]],Continue[];];*)
(**)
(*PossibilityList=Append[PossibilityList,m];*)
(*];*)
(*PossibilityList]*)


(* ::Subsubsection::Closed:: *)
(*No Anyon Permutation*)


(* ::Input:: *)
(*zero0=p6mCheckLSM[zero,0,0,0];*)
(*a0=p6mCheckLSM[a,0,0,0];*)
(*c0=p6mCheckLSM[c,0,0,0];*)
(*ac0=p6mCheckLSM[ac,0,0,0];*)
(**)
(*Length[zero0]*)
(*Length[a0]*)
(*Length[c0]*)
(*Length[ac0]*)


(* ::Subsubsection::Closed:: *)
(*With Anyon Permutation*)


(* ::Input:: *)
(*Do[If[i1!=0||i2!=0||i3!=0,Print[p6mCheckLSM[zero,i1,i2,i3]];],{i1,0,1},{i2,0,1},{i3,0,1}]*)


(* ::Input:: *)
(*Do[If[i1!=0||i2!=0||i3!=0,Print[p6mCheckLSM[a,i1,i2,i3]];],{i1,0,1},{i2,0,1},{i3,0,1}]*)


(* ::Input:: *)
(*Do[If[i1!=0||i2!=0||i3!=0,Print[p6mCheckLSM[c,i1,i2,i3]];],{i1,0,1},{i2,0,1},{i3,0,1}]*)


(* ::Input:: *)
(*Do[If[i1!=0||i2!=0||i3!=0,Print[p6mCheckLSM[ac,i1,i2,i3]];],{i1,0,1},{i2,0,1},{i3,0,1}]*)


(* ::Chapter:: *)
(*Symmetry: p4m*)


(* ::Section:: *)
(*SO(3)*Z2T*)


(* ::Input:: *)
(*zero= ConstantArray[0,30];*)
(*a = ConstantArray[0,30];a[[3]]=1;a[[5]]=1;*)
(*b = ConstantArray[0, 30];b[[12]]=1;b[[15]]=1;*)
(*c=ConstantArray[0, 30];c[[11]]=1;c[[14]]=1;*)
(*ab = Mod[a+b,2];*)
(*ac=Mod[a+c,2];*)
(*bc=Mod[b+c,2];*)
(*abc=Mod[a+b+c,2];*)


(* ::Input:: *)
(*p4mBxy[g1_List, g2_List]:=Which[Mod[g1[[3]],2]==0,g1[[2]]*g2[[1]],Mod[g1[[3]],2]==1, (g1[[2]]+ g2[[1]])*(g2[[2]])]*)
(*p4mBc2[g1_List, g2_List]:=(g1[[3]]+(-1)^(g1[[4]])*g2[[3]]-Mod[g1[[3]]+(-1)^(g1[[4]])* g2[[3]],4])/4*)


(* ::Input:: *)
(*P[x_Integer]:=Mod[x, 2];*)
(*Pc[x_Integer]:=1-P[x];*)
(*Action[g_List]:={g[[2]],g[[1]]};*)
(**)
(*p4maction1w1[g1_List, g2_List]:={g1[[1]]*g2[[4]],g1[[2]]*g2[[4]]};*)
(*p4maction1w2[g1_List,g2_List]:={(Quotient[g1[[3]],2]+Mod[g1[[3]],2]+g1[[3]]*g1[[4]])*g2[[4]],(Quotient[g1[[3]],2]+g1[[4]]+g1[[3]]*g1[[4]])*g2[[4]]};*)
(*p4maction1w3[g1_List,g2_List]:={(Quotient[g1[[3]],2]+Mod[g1[[3]],2]+g1[[3]]*g1[[4]])*(P[g1[[3]]]*g2[[1]]+Pc[g1[[3]]]*g2[[2]]),(Quotient[g1[[3]],2]+g1[[4]]+g1[[3]]*g1[[4]])*(P[g1[[3]]]*g2[[2]]+Pc[g1[[3]]]*g2[[1]])};*)
(*p4maction1w4[g1_List,g2_List]:={g1[[1]]*g2[[5]],g1[[2]]*g2[[5]]};*)
(*p4maction1w5[g1_List,g2_List]:={(Quotient[g1[[3]],2]+Mod[g1[[3]],2]+g1[[3]]*g1[[4]])*g2[[5]],(Quotient[g1[[3]],2]+g1[[4]]+g1[[3]]*g1[[4]])*g2[[5]]};*)
(**)
(*p4maction2w1[g1_List, g2_List]:={(Quotient[g1[[3]],2])(P[g1[[3]]+g1[[4]]]*(Quotient[g2[[3]],2])+Pc[g1[[3]]+g1[[4]]]*(Quotient[g2[[3]],2]+Mod[g2[[3]],2])),(Quotient[g1[[3]],2]+Mod[g1[[3]],2])(P[g1[[3]]+g1[[4]]]*(Quotient[g2[[3]],2]+Mod[g2[[3]],2])+Pc[g1[[3]]+g1[[4]]]*(Quotient[g2[[3]],2]))};*)
(*p4maction2w2[g1_List,g2_List]:={(Quotient[g1[[3]],2])*g2[[5]],(Quotient[g1[[3]],2]+Mod[g1[[3]],2])*g2[[5]]};*)
(**)


(* ::Input:: *)
(*p4mSFClass[g1_List,g2_List,SF_List,actionTrans_,actionC_,actionM_, actionT_]:=Mod[*)
(*Which[actionTrans==0&&actionC==0&&actionM==0&&actionT==0,*)
(*p4mBxy[g1,g2]*{SF[[1]][[1]],SF[[2]][[1]]}+p4mBc2[g1,g2]*{SF[[1]][[2]],SF[[2]][[2]]}+(g1[[1]]+g1[[2]])*(g2[[1]]+g2[[2]])*{SF[[1]][[3]],SF[[2]][[3]]}+(g1[[1]]+g1[[2]])*g2[[4]]*{SF[[1]][[4]],SF[[2]][[4]]}+g1[[3]]*g2[[3]]*{SF[[1]][[5]],SF[[2]][[5]]}+g1[[4]]*g2[[4]]*{SF[[1]][[6]],SF[[2]][[6]]}+(g1[[1]]+g1[[2]])*g2[[5]]*{SF[[1]][[7]],SF[[2]][[7]]}+g1[[3]]*g2[[5]]*{SF[[1]][[8]],SF[[2]][[8]]}+g1[[4]]*g2[[5]]*{SF[[1]][[9]],SF[[2]][[9]]}+g1[[5]]*g2[[5]]*{SF[[1]][[10]],SF[[2]][[10]]}+g1[[6]]*g2[[6]]*{SF[[1]][[11]],SF[[2]][[11]]},*)
(*actionT==1,*)
(*p4mBxy[g1,g2]*{SF[[1]],SF[[1]]}+p4mBc2[g1,g2]*{SF[[2]],SF[[2]]}+(g1[[1]]+g1[[2]])*(g2[[1]]+g2[[2]])*{SF[[3]],SF[[3]]}+(g1[[1]]+g1[[2]])*g2[[4]]*{SF[[4]],SF[[4]]}+g1[[3]]*g2[[3]]*{SF[[5]],SF[[5]]}+g1[[4]]*g2[[4]]*{SF[[6]],SF[[6]]}+g1[[6]]*g2[[6]]*{SF[[7]],SF[[7]]},*)
(*actionTrans==0&&actionC==0&&actionM==1&&actionT==0,*)
(*p4mBxy[g1,g2]*{SF[[1]],SF[[1]]}+p4mBc2[g1,g2]*{SF[[2]],SF[[2]]}+(g1[[1]]+g1[[2]])*(g2[[1]]+g2[[2]])*{SF[[3]],SF[[3]]}+(g1[[1]]+g1[[2]])*g2[[5]]*{SF[[4]],SF[[4]]}+g1[[3]]*g2[[5]]*{SF[[5]],SF[[5]]}+g1[[5]]*g2[[5]]*{SF[[6]],SF[[6]]}+g1[[6]]*g2[[6]]*{SF[[7]],SF[[7]]},*)
(*actionTrans==0&&actionC==1&&actionM==0&&actionT==0,*)
(*p4mBxy[g1,g2]*{SF[[1]],SF[[1]]}+p4mBc2[g1,g2]*{SF[[2]],SF[[2]]}+g1[[5]]*g2[[5]]*{SF[[5]],SF[[5]]}+g1[[6]]*g2[[6]]*{SF[[6]],SF[[6]]}+SF[[5]]*p4maction1w1[g1,g2]+SF[[6]]*p4maction1w2[g1,g2]+SF[[7]]*p4maction1w3[g1,g2]+SF[[8]]*p4maction1w4[g1,g2]+SF[[9]]*p4maction1w5[g1,g2]+Action[SF[[10]]*p4maction1w1[g1,g2]+SF[[11]]*p4maction1w2[g1,g2]+SF[[12]]*p4maction1w3[g1,g2]+SF[[13]]*p4maction1w4[g1,g2]+SF[[14]]*p4maction1w5[g1,g2]],*)
(*actionTrans==0&&actionC==1&&actionM==1&&actionT==0,*)
(*p4mBxy[g1,g2]*{SF[[1]],SF[[1]]}+p4mBc2[g1,g2]*{SF[[2]],SF[[2]]}+(g1[[1]]+g1[[2]])*(g2[[1]]+g2[[2]])*{SF[[3]],SF[[3]]}+(g1[[1]]+g1[[2]])*g2[[5]]*{SF[[4]],SF[[4]]}+g1[[5]]*g2[[5]]*{SF[[5]],SF[[5]]}+g1[[6]]*g2[[6]]*{SF[[6]],SF[[6]]}+SF[[7]]*p4maction2w1[g1,g2]+SF[[8]]*p4maction2w2[g1,g2]+Action[SF[[9]]*p4maction2w1[g1,g2]+SF[[10]]*p4maction2w2[g1,g2]]*)
(*],2]*)


(* ::Input:: *)
(*p4mCheckIndZ2T[g_List,SF_List,actionTrans_,actionC_,actionM_,actionT_]:=Module[{flag,s,Ind},*)
(*flag = Mod[(g[[1]]+g[[2]])*actionTrans+g[[3]]*actionC+g[[4]]*actionM+g[[5]]*actionT,2];*)
(*Ind=1;*)
(*If[flag==0,*)
(*s=p4mSFClass[g,g,SF,actionTrans,actionC,actionM,actionT];*)
(*Ind=IndicatorZ2TS1[s[[1]],s[[2]]];*)
(*];*)
(*Ind];*)
(**)
(*p4mCheckIndZ2TZ2T[g1_List,g2_List,SF_List,actionTrans_,actionC_,actionM_,actionT_]:=Module[{flag1,flag2,s,t,st,Ind},*)
(*flag1= Mod[(g1[[1]]+g1[[2]])*actionTrans+g1[[3]]*actionC+g1[[4]]*actionM+g1[[5]]*actionT,2];*)
(*flag2= Mod[(g2[[1]]+g2[[2]])*actionTrans+g2[[3]]*actionC+g2[[4]]*actionM+g2[[5]]*actionT,2];*)
(*Ind=1;*)
(*If[flag1==0&&flag2==0,*)
(*s=p4mSFClass[g1,g1,SF,actionTrans,actionC,actionM,actionT];*)
(*t=p4mSFClass[g2,g2,SF,actionTrans,actionC,actionM,actionT];*)
(*st=Mod[p4mSFClass[g1,g2,SF,actionTrans,actionC,actionM,actionT]+p4mSFClass[g2,g1,SF,actionTrans,actionC,actionM,actionT],2];*)
(*Ind=IndicatorZ2TZ2TS1[s[[1]],s[[2]],t[[1]],t[[2]],st[[1]],st[[2]]];];*)
(*If[flag1==1&&flag2==0,*)
(*t=p4mSFClass[g2,g2,SF,actionTrans,actionC,actionM,actionT];*)
(*Ind=IndicatorZ2TZ2TS2[t[[1]]];];*)
(*If[flag1==0&&flag2==1,*)
(*t=p4mSFClass[g1,g1,SF,actionTrans,actionC,actionM,actionT];*)
(*Ind=IndicatorZ2TZ2TS2[t[[1]]];];*)
(*If[flag1==1&&flag2==1,*)
(*st=Mod[p4mSFClass[g1,g1,SF,actionTrans,actionC,actionM,actionT]+p4mSFClass[g2,g2,SF,actionTrans,actionC,actionM,actionT]+p4mSFClass[g1,g2,SF,actionTrans,actionC,actionM,actionT]+p4mSFClass[g2,g1,SF,actionTrans,actionC,actionM,actionT],2];*)
(*Ind=IndicatorZ2TZ2TS2[st[[1]]];];*)
(*Ind];*)
(**)
(*p4mCheckIndSO3[SF_List,actionTrans_,actionC_,actionM_,actionT_]:=If[actionTrans==0&actionC==0&&actionM==0&&actionT==0,IndicatorSO3[SF[[1]][[11]],SF[[2]][[11]]],IndicatorSO3[SF[[7]],SF[[7]]]];*)
(**)
(*p4mCheckIndZ2Z2[g_List,SF_List,actionTrans_,actionC_,actionM_,actionT_]:=Module[{flag,s,st,Ind},*)
(*flag= Mod[(g[[1]]+g[[2]])*actionTrans+g[[3]]*actionC+g[[4]]*actionM+g[[5]]*actionT,2];*)
(*Ind =1;*)
(*If[flag==0,*)
(*st=If[actionTrans==0&&actionC==0&&actionM==0&&actionT==0,{SF[[1]][[11]],SF[[2]][[11]]},{SF[[7]],SF[[7]]}];*)
(*s=Mod[p4mSFClass[g,g,SF,actionC,actionM,actionT]+st,2];*)
(*Ind=IndicatorZ2Z2S1[s[[1]],s[[2]],st[[1]],st[[2]]];*)
(*];*)
(*Ind]*)


(* ::Input:: *)
(*p4mCheckLSM[LSMList_List,actionTrans_,actionC_,actionM_,actionT_]:=Module[{m,Dim,SFList,PossibilityList},*)
(*PossibilityList = {};*)
(**)
(*Dim=Which[actionTrans==0&&actionC==0&&actionM==0&&actionT==0,22,*)
(*actionTrans==0&&actionC==1&&actionM==0&&actionT==0,14,*)
(*actionTrans==0&&actionC==1&&actionM==1&&actionT==0,10,*)
(*actionTrans==1&&actionC==actionM&&actionT==0,11,*)
(*True,7];*)
(**)
(*For[m=0,m<2^Dim,m++,*)
(*SFList=PadLeft[IntegerDigits[m,2],Dim];*)
(**)
(*If[actionTrans==0&&actionC==0&&actionM==0&&actionT==0,*)
(*If[Quotient[m,2^11]<Mod[m,2^11],Continue[];];SFList={SFList[[1;;11]],SFList[[12;;22]]};];*)
(*If[actionTrans==0&&actionC==1&&actionM==0&&actionT==0,*)
(*If[Quotient[Mod[m,2^10],2^5]<Mod[Mod[m,2^10],2^5],Continue[];];];*)
(**)
(*If[p4mCheckIndZ2T[{0,0,0,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[1]],Continue[];];*)
(*If[p4mCheckIndZ2T[{0,0,0,1,0,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[2]],Continue[];];*)
(**)
(*If[p4mCheckIndZ2T[{0,0,2,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[3]],Continue[];];*)
(*If[p4mCheckIndZ2T[{0,0,1,1,0,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[4]],Continue[];];*)
(**)
(*If[p4mCheckIndZ2TZ2T[{0,0,0,0,1,0},{0,0,2,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[5]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,0,0,1,0},{0,0,0,1,0,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[6]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,1,1,0,0},{0,0,0,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[7]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,2,0,1,0},{0,0,0,1,0,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[8]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,1,1,0,0},{0,0,2,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[9]],Continue[];];*)
(**)
(*If[p4mCheckIndZ2T[{1,0,0,1,0,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[10]],Continue[];];*)
(*If[p4mCheckIndZ2T[{1,0,2,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[11]],Continue[];];*)
(*If[p4mCheckIndZ2T[{1,1,2,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[12]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{1,0,0,1,0,0},{0,0,0,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[13]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,0,0,1,0},{1,0,2,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[14]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,0,0,1,0},{1,1,2,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[15]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,0,1,0,0},{0,1,2,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[16]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,0,1,0,0},{0,1,2,1,0,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[17]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,1,1,0,0},{1,-1,2,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[18]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{1,0,0,1,0,0},{1,1,2,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[19]],Continue[];];*)
(**)
(*If[p4mCheckIndSO3[SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[20]],Continue[];];*)
(**)
(*If[p4mCheckIndZ2T[{0,0,0,0,1,1},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[21]],Continue[];];*)
(*If[p4mCheckIndZ2T[{0,0,0,1,0,1},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[22]],Continue[];];*)
(*If[p4mCheckIndZ2T[{0,0,2,0,1,1},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[23]],Continue[];];*)
(*If[p4mCheckIndZ2T[{0,0,1,1,0,1},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[24]],Continue[];];*)
(*If[p4mCheckIndZ2T[{1,0,0,1,0,1},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[25]],Continue[];];*)
(*If[p4mCheckIndZ2T[{1,0,2,0,1,1},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[26]],Continue[];];*)
(*If[p4mCheckIndZ2T[{1,1,2,0,1,1},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[27]],Continue[];];*)
(**)
(*If[p4mCheckIndZ2Z2[{0,0,1,1,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[28]],Continue[];];*)
(*If[p4mCheckIndZ2Z2[{0,0,0,1,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[29]],Continue[];];*)
(*If[p4mCheckIndZ2Z2[{1,0,0,1,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[30]],Continue[];];*)
(**)
(*PossibilityList=Append[PossibilityList,m];*)
(*];*)
(*PossibilityList]*)


(* ::Subsubsection:: *)
(*No Anyon Permutation*)


(* ::Input:: *)
(*(*Given every symmetry fractionalization pattern, check whether it equals the anomaly written by LSMList*)*)
(*p4mCheckLSM0[LSMList_List]:=Module[{m,SFList,PossibilityList},*)
(*PossibilityList = {};*)
(*For[m=0,m<2^22,m++,*)
(*SFList=PadLeft[IntegerDigits[m,2],22];*)
(*SFList={SFList[[1;;11]],SFList[[12;;22]]};*)
(**)
(*If[Quotient[m,2^11]>Mod[m,2^11],Continue[];];*)
(**)
(*If[p4mCheckIndZ2T[{0,0,0,0,1,0},SFList,0,0,0,0]!=(-1)^LSMList[[1]],Continue[];];*)
(*If[p4mCheckIndZ2T[{0,0,0,1,0,0},SFList,0,0,0,0]!=(-1)^LSMList[[2]],Continue[];];*)
(**)
(*If[p4mCheckIndZ2T[{0,0,2,0,1,0},SFList,0,0,0,0]!=(-1)^LSMList[[3]],Continue[];];*)
(*If[p4mCheckIndZ2T[{0,0,1,1,0,0},SFList,0,0,0,0]!=(-1)^LSMList[[4]],Continue[];];*)
(**)
(*If[p4mCheckIndZ2TZ2T[{0,0,0,0,1,0},{0,0,2,0,1,0},SFList,0,0,0,0]!=(-1)^LSMList[[5]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,0,0,1,0},{0,0,0,1,0,0},SFList,0,0,0,0]!=(-1)^LSMList[[6]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,1,1,0,0},{0,0,0,0,1,0},SFList,0,0,0,0]!=(-1)^LSMList[[7]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,2,0,1,0},{0,0,0,1,0,0},SFList,0,0,0,0]!=(-1)^LSMList[[8]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,1,1,0,0},{0,0,2,0,1,0},SFList,0,0,0,0]!=(-1)^LSMList[[9]],Continue[];];*)
(**)
(*If[p4mCheckIndZ2T[{1,0,0,1,0,0},SFList,0,0,0,0]!=(-1)^LSMList[[10]],Continue[];];*)
(*If[p4mCheckIndZ2T[{1,0,2,0,1,0},SFList,0,0,0,0]!=(-1)^LSMList[[11]],Continue[];];*)
(*If[p4mCheckIndZ2T[{1,1,2,0,1,0},SFList,0,0,0,0]!=(-1)^LSMList[[12]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{1,0,0,1,0,0},{0,0,0,0,1,0},SFList,0,0,0,0]!=(-1)^LSMList[[13]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,0,0,1,0},{1,0,2,0,1,0},SFList,0,0,0,0]!=(-1)^LSMList[[14]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,0,0,1,0},{1,1,2,0,1,0},SFList,0,0,0,0]!=(-1)^LSMList[[15]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,0,1,0,0},{0,1,2,0,1,0},SFList,0,0,0,0]!=(-1)^LSMList[[16]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,0,1,0,0},{0,1,2,1,0,0},SFList,0,0,0,0]!=(-1)^LSMList[[17]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,1,1,0,0},{1,-1,2,0,1,0},SFList,0,0,0,0]!=(-1)^LSMList[[18]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{1,0,0,1,0,0},{1,1,2,0,1,0},SFList,0,0,0,0]!=(-1)^LSMList[[19]],Continue[];];*)
(**)
(*If[p4mCheckIndSO3[SFList,0,0,0,0]!=(-1)^LSMList[[20]],Continue[];];*)
(**)
(*If[p4mCheckIndZ2T[{0,0,0,0,1,1},SFList,0,0,0,0]!=(-1)^LSMList[[21]],Continue[];];*)
(*If[p4mCheckIndZ2T[{0,0,0,1,0,1},SFList,0,0,0,0]!=(-1)^LSMList[[22]],Continue[];];*)
(*If[p4mCheckIndZ2T[{0,0,2,0,1,1},SFList,0,0,0,0]!=(-1)^LSMList[[23]],Continue[];];*)
(*If[p4mCheckIndZ2T[{0,0,1,1,0,1},SFList,0,0,0,0]!=(-1)^LSMList[[24]],Continue[];];*)
(*If[p4mCheckIndZ2T[{1,0,0,1,0,1},SFList,0,0,0,0]!=(-1)^LSMList[[25]],Continue[];];*)
(*If[p4mCheckIndZ2T[{1,0,2,0,1,1},SFList,0,0,0,0]!=(-1)^LSMList[[26]],Continue[];];*)
(*If[p4mCheckIndZ2T[{1,1,2,0,1,1},SFList,0,0,0,0]!=(-1)^LSMList[[27]],Continue[];];*)
(**)
(*If[p4mCheckIndZ2Z2[{0,0,1,1,1,0},SFList,0,0,0,0]!=(-1)^LSMList[[28]],Continue[];];*)
(*If[p4mCheckIndZ2Z2[{0,0,0,1,1,0},SFList,0,0,0,0]!=(-1)^LSMList[[29]],Continue[];];*)
(*If[p4mCheckIndZ2Z2[{1,0,0,1,1,0},SFList,0,0,0,0]!=(-1)^LSMList[[30]],Continue[];];*)
(**)
(*PossibilityList=Append[PossibilityList,m];*)
(*];*)
(*PossibilityList]*)


(* ::Input:: *)
(*zeroPossibilityList=p4mCheckLSM0[zero];*)
(*Length[zeroPossibilityList]*)


(* ::Input:: *)
(*aPossibilityList=p4mCheckLSM0[a];*)
(*Length[aPossibilityList]*)


(* ::Input:: *)
(*bPossibilityList=p4mCheckLSM0[b];*)
(*Length[bPossibilityList]*)


(* ::Input:: *)
(*cPossibilityList=p4mCheckLSM0[c];*)
(*Length[cPossibilityList]*)


(* ::Input:: *)
(*abPossibilityList=p4mCheckLSM0[ab];*)
(*Length[abPossibilityList]*)


(* ::Input:: *)
(*acPossibilityList=p4mCheckLSM0[ac];*)
(*Length[acPossibilityList]*)


(* ::Input:: *)
(*bcPossibilityList=p4mCheckLSM0[bc];*)
(*Length[aPossibilityList]*)


(* ::Input:: *)
(*abcPossibilityList=p4mCheckLSM0[abc];*)
(*Length[aPossibilityList]*)


(* ::Subsubsection:: *)
(*With Permutation*)


(* ::Input:: *)
(*(*Given every symmetry fractionalization pattern, check whether it equals the anomaly written by LSMList*)*)
(*p4mCheckLSM1[LSMList_List,actionTrans_,actionC_,actionM_,actionT_]:=Module[{m,Dim,SFList,PossibilityList},*)
(*PossibilityList = {};*)
(**)
(*Dim=Which[actionTrans==0&&actionC==0&&actionM==0&&actionT==0,22,*)
(*actionTrans==0&&actionC==1&&actionM==0&&actionT==0,14,*)
(*actionTrans==0&&actionC==1&&actionM==1&&actionT==0,10,*)
(*actionTrans==1&&actionC==actionM&&actionT==0,11,*)
(*True,7];*)
(**)
(*For[m=0,m<2^Dim,m++,*)
(*SFList=PadLeft[IntegerDigits[m,2],Dim];*)
(**)
(*If[actionTrans==0&&actionC==0&&actionM==0&&actionT==0,*)
(*If[Quotient[m,2^11]>Mod[m,2^11],Continue[];];SFList={SFList[[1;;11]],SFList[[12;;22]]};];*)
(*If[actionTrans==0&&actionC==1&&actionM==0&&actionT==0,*)
(*];*)
(**)
(*If[p4mCheckIndZ2T[{0,0,0,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[1]],Continue[];];*)
(*If[p4mCheckIndZ2T[{0,0,0,1,0,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[2]],Continue[];];*)
(**)
(*If[p4mCheckIndZ2T[{0,0,2,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[3]],Continue[];];*)
(*If[p4mCheckIndZ2T[{0,0,1,1,0,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[4]],Continue[];];*)
(**)
(*If[p4mCheckIndZ2TZ2T[{0,0,0,0,1,0},{0,0,2,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[5]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,0,0,1,0},{0,0,0,1,0,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[6]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,1,1,0,0},{0,0,0,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[7]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,2,0,1,0},{0,0,0,1,0,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[8]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,1,1,0,0},{0,0,2,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[9]],Continue[];];*)
(**)
(*If[p4mCheckIndZ2T[{1,0,0,1,0,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[10]],Continue[];];*)
(*If[p4mCheckIndZ2T[{1,0,2,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[11]],Continue[];];*)
(*If[p4mCheckIndZ2T[{1,1,2,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[12]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{1,0,0,1,0,0},{0,0,0,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[13]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,0,0,1,0},{1,0,2,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[14]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,0,0,1,0},{1,1,2,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[15]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,0,1,0,0},{0,1,2,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[16]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,0,1,0,0},{0,1,2,1,0,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[17]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{0,0,1,1,0,0},{1,-1,2,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[18]],Continue[];];*)
(*If[p4mCheckIndZ2TZ2T[{1,0,0,1,0,0},{1,1,2,0,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[19]],Continue[];];*)
(**)
(*If[p4mCheckIndSO3[SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[20]],Continue[];];*)
(**)
(*If[p4mCheckIndZ2T[{0,0,0,0,1,1},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[21]],Continue[];];*)
(*If[p4mCheckIndZ2T[{0,0,0,1,0,1},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[22]],Continue[];];*)
(*If[p4mCheckIndZ2T[{0,0,2,0,1,1},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[23]],Continue[];];*)
(*If[p4mCheckIndZ2T[{0,0,1,1,0,1},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[24]],Continue[];];*)
(*If[p4mCheckIndZ2T[{1,0,0,1,0,1},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[25]],Continue[];];*)
(*If[p4mCheckIndZ2T[{1,0,2,0,1,1},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[26]],Continue[];];*)
(*If[p4mCheckIndZ2T[{1,1,2,0,1,1},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[27]],Continue[];];*)
(**)
(*If[p4mCheckIndZ2Z2[{0,0,1,1,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[28]],Continue[];];*)
(*If[p4mCheckIndZ2Z2[{0,0,0,1,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[29]],Continue[];];*)
(*If[p4mCheckIndZ2Z2[{1,0,0,1,1,0},SFList,actionTrans,actionC,actionM,actionT]!=(-1)^LSMList[[30]],Continue[];];*)
(**)
(*PossibilityList=Append[PossibilityList,m];*)
(*];*)
(*PossibilityList]*)


(* ::Input:: *)
(*Do[Print[p4mCheckLSM1[zero,i1,i2,i3,1]],{i1,0,1},{i2,0,1},{i3,0,1}];*)
(*Print[p4mCheckLSM1[zero,0,0,1,0]]*)


(* ::Input:: *)
(*Do[Print[p4mCheckLSM1[a,i1,i2,i3,1]],{i1,0,1},{i2,0,1},{i3,0,1}];*)
(*Print[p4mCheckLSM1[a,0,0,1,0]]*)


(* ::Input:: *)
(*Do[Print[p4mCheckLSM1[b,i1,i2,i3,1]],{i1,0,1},{i2,0,1},{i3,0,1}];*)
(*Print[p4mCheckLSM1[b,0,0,1,0]]*)


(* ::Input:: *)
(*Do[Print[p4mCheckLSM1[c,i1,i2,i3,1]],{i1,0,1},{i2,0,1},{i3,0,1}];*)
(*Print[p4mCheckLSM1[c,0,0,1,0]]*)


(* ::Input:: *)
(*Do[Print[p4mCheckLSM1[ab,i1,i2,i3,1]],{i1,0,1},{i2,0,1},{i3,0,1}];*)
(*Print[p4mCheckLSM1[ab,0,0,1,0]]*)


(* ::Input:: *)
(*Do[Print[p4mCheckLSM1[ac,i1,i2,i3,1]],{i1,0,1},{i2,0,1},{i3,0,1}];*)
(*Print[p4mCheckLSM1[ac,0,0,1,0]]*)


(* ::Input:: *)
(*Do[Print[p4mCheckLSM1[bc,i1,i2,i3,1]],{i1,0,1},{i2,0,1},{i3,0,1}];*)
(*Print[p4mCheckLSM1[bc,0,0,1,0]]*)


(* ::Input:: *)
(*Do[Print[p4mCheckLSM1[abc,i1,i2,i3,1]],{i1,0,1},{i2,0,1},{i3,0,1}];*)
(*Print[p4mCheckLSM1[abc,0,0,1,0]]*)




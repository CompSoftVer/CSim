(*
    Author:      David Sanan
    Maintainer:  David Sanan, sanan at ntu edu sg
    License:     LGPL
*)

(*  Title:      SmallStepCon.thy
    Author:     David Sanan, NTU

Copyright (C) 2015-2016 David Sanan 
Some rights reserved, NTU
This library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as
published by the Free Software Foundation; either version 2.1 of the
License, or (at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
USA
*)

section {* Small-Step Semantics and Infinite Computations*} 

theory SmallStepCon imports "EmbSimpl.SmallStep" "SemanticCon"  
                            "TerminationCon"
                            (* "Sep_Algebra.Sep_Heap_Instance" 
                            "Actions.ActionsSemantics" *)
begin

text {* The redex of a statement is the substatement, which is actually altered
by the next step in the small-step semantics.
*}
primrec redex:: "('s,'p,'f,'e)com \<Rightarrow> ('s,'p,'f,'e)com"
where
"redex Skip = Skip" |
"redex (Basic f e) = (Basic f e)" |
"redex (Spec r e) = (Spec r e)" |
"redex (Seq c\<^sub>1 c\<^sub>2) = redex c\<^sub>1" |
"redex (Cond b c\<^sub>1 c\<^sub>2) = (Cond b c\<^sub>1 c\<^sub>2)" |
"redex (While b c) = (While b c)" |
"redex (Call p) = (Call p)" |
"redex (DynCom d) = (DynCom d)" |
"redex (Guard f b c) = (Guard f b c)" |
"redex (Throw) = Throw" |
"redex (Catch c\<^sub>1 c\<^sub>2) = redex c\<^sub>1" |
"redex (Await b c e) = (Await b c e)"



subsection {*Small-Step Computation: @{text "\<Gamma>\<turnstile>\<^sub>c(c, s) \<rightarrow> (c', s')"}*}
type_synonym ('s,'p,'f,'e) config = "('s,'p,'f,'e)com  \<times> ('s,'f) xstate"

inductive 
      "step_e"::"[('s,'p,'f,'e) body,('s,'p,'f,'e) config,('s,'p,'f,'e) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sub>e/ _)" [81,81,81] 100)  
  for \<Gamma>::"('s,'p,'f,'e) body"
where
Env: "\<Gamma>\<turnstile>\<^sub>c (Ps, Normal s) \<rightarrow>\<^sub>e (Ps, t)"
|Env_n: "(\<forall>t'. t\<noteq>Normal t') \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c (Ps, t) \<rightarrow>\<^sub>e (Ps, t)"

lemma etranE: "\<Gamma>\<turnstile>\<^sub>c c \<rightarrow>\<^sub>e c' \<Longrightarrow> (\<And>P s t. c = (P, s) \<Longrightarrow> c' = (P, t) \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (induct c, induct c', erule  step_e.cases, blast)

inductive_cases stepe_Normal_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>c(Ps,Normal s) \<rightarrow>\<^sub>e (Ps,t)"

inductive_cases stepe_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>c(Ps,s) \<rightarrow>\<^sub>e (Ps,t)"

inductive_cases stepe_not_norm_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>c(Ps,s) \<rightarrow>\<^sub>e (Ps,Abrupt t)"
 "\<Gamma>\<turnstile>\<^sub>c(Ps,s) \<rightarrow>\<^sub>e (Ps,Stuck)"
 "\<Gamma>\<turnstile>\<^sub>c(Ps,s) \<rightarrow>\<^sub>e (Ps,Fault t)"
 "\<Gamma>\<turnstile>\<^sub>c(Ps,s) \<rightarrow>\<^sub>e (Ps,Normal t)"

lemma env_c_c'_false:
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', s')" 
   shows "~(c=c')  \<Longrightarrow> P"
using step_m etranE by blast

lemma eenv_normal_s'_normal_s:
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', Normal s')" 
   shows "(\<And>s1. s\<noteq>Normal s1)  \<Longrightarrow> P"
using step_m 
by (cases, auto)

lemma env_normal_s'_normal_s:
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', Normal s') " 
   shows "\<exists>s1. s= Normal s1"
using step_m 
by (cases, auto)

lemma env_c_c':
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', s')" 
   shows "(c=c')"
using env_c_c'_false step_m by fastforce 

lemma env_normal_s:
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', s') \<and> s\<noteq>s'" 
   shows "\<exists>sa. s = Normal sa"
using prod.inject step_e.cases step_m by fastforce

lemma env_not_normal_s:
   assumes a1:"\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', s')" and  a2:"(\<forall>t. s\<noteq>Normal t)" 
   shows "s=s'"
using a1 a2
by (cases rule:step_e.cases,auto) 

lemma env_not_normal_s_not_norma_t:
   assumes a1:"\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', s')" and  a2:"(\<forall>t. s\<noteq>Normal t)" 
   shows "(\<forall>t. s'\<noteq>Normal t)"
using a1 a2 env_not_normal_s
by blast

lemma stepe_not_Fault_f_end:
  assumes step_e: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, s) \<rightarrow>\<^sub>e (c\<^sub>1', s')"
  shows "s'\<notin> Fault ` f \<Longrightarrow> s \<notin> Fault ` f"
proof (cases s) 
  case (Fault f')
    assume s'_f:"s' \<notin> Fault ` f" and
           "s = Fault f'" 
    then have "s=s'" using step_e 
    using env_normal_s xstate.distinct(3) by blast  
  thus ?thesis using s'_f Fault by blast
qed (auto)

inductive       
      "stepc"::"[('s,'p,'f,'e) body,('s,'p,'f,'e) config,('s,'p,'f,'e) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>/ _)" [81,81,81] 100)  
  for \<Gamma>::"('s,'p,'f,'e) body"
where

  Basicc: "\<Gamma>\<turnstile>\<^sub>c(Basic f e,Normal s) \<rightarrow> (Skip,Normal (f s))"

| Specc: "(s,t) \<in> r \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(Spec r e,Normal s) \<rightarrow> (Skip,Normal t)"
| SpecStuckc: "\<forall>t. (s,t) \<notin> r \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(Spec r e,Normal s) \<rightarrow> (Skip,Stuck)"

| Guardc: "s\<in>g \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(Guard f g c,Normal s) \<rightarrow> (c,Normal s)"
  
| GuardFaultc: "s\<notin>g \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(Guard f g c,Normal s) \<rightarrow> (Skip,Fault f)"


| Seqc: "\<Gamma>\<turnstile>\<^sub>c(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s')
        \<Longrightarrow> 
        \<Gamma>\<turnstile>\<^sub>c(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Seq c\<^sub>1' c\<^sub>2, s')"
| SeqSkipc: "\<Gamma>\<turnstile>\<^sub>c(Seq Skip c\<^sub>2,s) \<rightarrow> (c\<^sub>2, s)"
| SeqThrowc: "\<Gamma>\<turnstile>\<^sub>c(Seq Throw c\<^sub>2,Normal s) \<rightarrow> (Throw, Normal s)"

| CondTruec:  "s\<in>b \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(Cond b c\<^sub>1 c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>1,Normal s)"
| CondFalsec: "s\<notin>b \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(Cond b c\<^sub>1 c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s)"

| WhileTruec: "\<lbrakk>s\<in>b\<rbrakk> 
              \<Longrightarrow> 
              \<Gamma>\<turnstile>\<^sub>c(While b c,Normal s) \<rightarrow> (Seq c (While b c),Normal s)"

| WhileFalsec: "\<lbrakk>s\<notin>b\<rbrakk> 
               \<Longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c(While b c,Normal s) \<rightarrow> (Skip,Normal s)"


| Awaitc:  "\<lbrakk>s\<in>b; \<Gamma>1=\<Gamma>\<^sub>\<not>\<^sub>a ; \<Gamma>1\<turnstile>\<langle>ca1,Normal s\<rangle> \<Rightarrow> t; 
             \<not>(\<exists>t'. t = Abrupt t')\<rbrakk> \<Longrightarrow> 
            \<Gamma>\<turnstile>\<^sub>c(Await b ca1 e,Normal s) \<rightarrow> (Skip,t)"

| AwaitAbruptc: "\<lbrakk>s\<in>b; \<Gamma>1=\<Gamma>\<^sub>\<not>\<^sub>a ; \<Gamma>1\<turnstile>\<langle>ca1,Normal s\<rangle> \<Rightarrow> t; 
                  t = Abrupt t'\<rbrakk> \<Longrightarrow> 
                 \<Gamma>\<turnstile>\<^sub>c(Await b ca1 e,Normal s) \<rightarrow> (Throw,Normal t')"

| Callc: "\<lbrakk>\<Gamma> p = Some bdy ; bdy\<noteq>Call p\<rbrakk> \<Longrightarrow>
         \<Gamma>\<turnstile>\<^sub>c(Call p,Normal s) \<rightarrow> (bdy,Normal s)"

| CallUndefinedc: "\<Gamma> p=None \<Longrightarrow>
         \<Gamma>\<turnstile>\<^sub>c(Call p,Normal s) \<rightarrow> (Skip,Stuck)"

| DynComc: "\<Gamma>\<turnstile>\<^sub>c(DynCom c,Normal s) \<rightarrow> (c s,Normal s)"

| Catchc: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s')\<rbrakk>
          \<Longrightarrow>
          \<Gamma>\<turnstile>\<^sub>c(Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Catch c\<^sub>1' c\<^sub>2,s')"

| CatchThrowc: "\<Gamma>\<turnstile>\<^sub>c(Catch Throw c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s)"
| CatchSkipc: "\<Gamma>\<turnstile>\<^sub>c(Catch Skip c\<^sub>2,s) \<rightarrow> (Skip,s)"

| FaultPropc:  "\<lbrakk>c\<noteq>Skip; redex c = c\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(c,Fault f) \<rightarrow> (Skip,Fault f)"
| StuckPropc:  "\<lbrakk>c\<noteq>Skip; redex c = c\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(c,Stuck) \<rightarrow> (Skip,Stuck)"
| AbruptPropc: "\<lbrakk>c\<noteq>Skip; redex c = c\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(c,Abrupt f) \<rightarrow> (Skip,Abrupt f)"
                                                              
lemmas stepc_induct = stepc.induct [of _ "(c,s)" "(c',s')", split_format (complete), case_names
Basicc Specc SpecStuckc Guardc GuardFaultc Seqc SeqSkipc SeqThrowc CondTruec CondFalsec
WhileTruec WhileFalsec Awaitc AwaitAbruptc Callc CallUndefinedc DynComc Catchc CatchThrowc CatchSkipc
FaultPropc StuckPropc AbruptPropc, induct set]


inductive_cases stepc_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>c(Skip,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Guard f g c,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Basic f e,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Spec r e,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Seq c1 c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Cond b c1 c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(While b c,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Await b c2 e,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Call p,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(DynCom c,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Throw,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> u"

inductive_cases stepc_not_normal_elim_cases:
 "\<Gamma>\<turnstile>\<^sub>c(Call p,Abrupt s) \<rightarrow> (p',s')"
 "\<Gamma>\<turnstile>\<^sub>c(Call p, Fault f) \<rightarrow> (p',s')"
 "\<Gamma>\<turnstile>\<^sub>c(Call p, Stuck) \<rightarrow> (p',s')"
 

lemma Guardc_not_c:"Guard f g c \<noteq> c"
proof (induct c)
qed auto

lemma Catch_not_c1:"Catch c1 c2 \<noteq> c1"
proof (induct c1)
qed auto

lemma Catch_not_c:"Catch c1 c2 \<noteq> c2"
proof (induct c2)
qed auto

lemma seq_not_eq1: "Seq c1 c2\<noteq>c1"
  by (induct c1) auto

lemma seq_not_eq2: "Seq c1 c2\<noteq>c2"
  by (induct c2) auto

lemma if_not_eq1: "Cond b c1 c2 \<noteq>c1"
  by (induct c1) auto

lemma if_not_eq2: "Cond b c1 c2\<noteq>c2"
  by (induct c2) auto


lemmas seq_and_if_not_eq [simp] = seq_not_eq1 seq_not_eq2 
seq_not_eq1 [THEN not_sym] seq_not_eq2 [THEN not_sym] 
if_not_eq1 if_not_eq2 if_not_eq1 [THEN not_sym] if_not_eq2 [THEN not_sym]
Catch_not_c1 Catch_not_c Catch_not_c1 [THEN not_sym] Catch_not_c[THEN not_sym] 
Guardc_not_c Guardc_not_c[THEN not_sym]

inductive_cases stepc_elim_cases_Seq_Seq:
"\<Gamma>\<turnstile>\<^sub>c(Seq c1 c2,s) \<rightarrow> (Seq c1' c2,s')" 

inductive_cases stepc_elim_cases_Seq_Seq1:
"\<Gamma>\<turnstile>\<^sub>c(Seq c1 c2,Fault f) \<rightarrow> (q,s')" 
thm stepc_elim_cases_Seq_Seq1

inductive_cases stepc_elim_cases_Catch_Catch:
"\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> (Catch c1' c2,s')" 

inductive_cases stepc_elim_cases_Catch_Catch1:
"\<Gamma>\<turnstile>\<^sub>c(Seq c1 c2,Fault f) \<rightarrow> (q,s')" 

inductive_cases stepc_elim_cases_Seq_skip:
"\<Gamma>\<turnstile>\<^sub>c(Seq Skip c2,s) \<rightarrow> u" 
"\<Gamma>\<turnstile>\<^sub>c(Seq (Guard f g c1) c2,s) \<rightarrow> u"


inductive_cases stepc_elim_cases_Catch_skip:
"\<Gamma>\<turnstile>\<^sub>c(Catch Skip c2,s) \<rightarrow> u"

inductive_cases stepc_elim_cases_Await_skip:
"\<Gamma>\<turnstile>\<^sub>c (Await b c e, Normal s) \<rightarrow> (Skip,t)"

inductive_cases stepc_elim_cases_Await_throw:
"\<Gamma>\<turnstile>\<^sub>c (Await b c e, Normal s) \<rightarrow> (Throw,t)"

inductive_cases stepc_elim_cases_Catch_throw:
"\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> (Throw, Normal s1)" 

inductive_cases stepc_elim_cases_Catch_skip_c2:
"\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> (c2,s)"

inductive_cases stepc_Normal_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>c(Skip,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Guard f g c,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Basic f e,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Spec r e,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Seq c1 c2,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Cond b c1 c2,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(While b c,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Await b c e,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Call p,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(DynCom c,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Throw,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,Normal s) \<rightarrow> u"


text \<open> The final configuration is either of the form @{text "(Skip,_)"} for normal
termination, or @{term "(Throw,Normal s)"} in case the program was started in 
a @{term "Normal"} state and terminated abruptly. The @{const "Abrupt"} state is not used to
model abrupt termination, in contrast to the big-step semantics. Only if the
program starts in an @{const "Abrupt"} states it ends in the same @{term "Abrupt"}
state.\<close>

definition final:: "('s,'p,'f,'e) config \<Rightarrow> bool" where
"final cfg \<equiv> (fst cfg=Skip \<or> ((fst cfg=Throw) \<and> (\<exists>s. snd cfg=Normal s)))"

definition final_valid::"('s,'p,'f,'e) config \<Rightarrow> bool" where
"final_valid cfg = ((fst cfg=Skip \<or> fst cfg=Throw) \<and> (\<exists>s. snd cfg=Normal s))"

abbreviation 
 "stepc_rtrancl" :: "[('s,'p,'f,'e) body,('s,'p,'f,'e) config,('s,'p,'f,'e) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sup>*/ _)" [81,81,81] 100)
 where                                
  "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sup>* cf1 \<equiv> ((CONST stepc \<Gamma>))\<^sup>*\<^sup>* cf0 cf1" 
  (* "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sup>* cf1 \<equiv> (CONST ((stepc \<Gamma>) \<union> (step_e \<Gamma>)))\<^sup>*\<^sup>* cf0 cf1" *)

abbreviation 
 "stepc_trancl" :: "[('s,'p,'f,'e) body,('s,'p,'f,'e) config,('s,'p,'f,'e) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sup>+/ _)" [81,81,81] 100)
 where
  "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sup>+ cf1 \<equiv> (CONST stepc \<Gamma>)\<^sup>+\<^sup>+ cf0 cf1"

lemma 
   assumes 
           step_a: "\<Gamma>\<turnstile>\<^sub>c(Await b c e, Normal s) \<rightarrow> (t,u)"
   shows step_await_step_c:"(\<Gamma>\<^sub>\<not>\<^sub>a)\<turnstile>(c, Normal s) \<rightarrow>\<^sup>* (sequential t,u)" 
using step_a
proof cases
  fix t1
  assume
      "(t, u) = (Skip, t1)" "s \<in> b" "(\<Gamma>\<^sub>\<not>\<^sub>a)\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> t1" "\<forall>t'. t1 \<noteq> Abrupt t'"
  thus ?thesis 
   by (cases u) 
   (auto intro: exec_impl_steps_Fault exec_impl_steps_Normal exec_impl_steps_Stuck)
next
  fix t1
  assume "(t, u) = (Throw, Normal t1)" "s \<in> b" "(\<Gamma>\<^sub>\<not>\<^sub>a)\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> Abrupt t1"
  thus ?thesis by (simp add: exec_impl_steps_Normal_Abrupt)
qed

lemma 
   assumes (* exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t" and
           b: "s \<in> b" and *)
           step_a: "\<Gamma>\<turnstile>\<^sub>c(Await b c e, Normal s) \<rightarrow> u"
   shows step_await_final1:"final u"
using step_a 
proof cases
  case  (1 t) thus "final u"  by (simp add: final_def)
next
  case (2 t)
  thus "final u" by (simp add: exec_impl_steps_Normal_Abrupt final_def)
qed

lemma step_Abrupt_end: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')"
  shows "s'=Abrupt x \<Longrightarrow> s=Abrupt x"
using step
by induct auto


lemma step_Stuck_end: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')"
  shows "s'=Stuck \<Longrightarrow> 
          s=Stuck \<or> 
          (\<exists>r x e. redex c\<^sub>1 = Spec r e \<and> s=Normal x \<and> (\<forall>t. (x,t)\<notin>r)) \<or> 
          (\<exists>p x. redex c\<^sub>1=  Call p \<and> s=Normal x \<and> \<Gamma> p = None) \<or>
          (\<exists>b c x e.  redex c\<^sub>1 = Await b c e \<and> s=Normal x \<and> x \<in> b \<and> (\<Gamma>\<^sub>\<not>\<^sub>a)\<turnstile>\<langle>c,s\<rangle>\<Rightarrow>s')"
using step
by induct auto

lemma step_Fault_end: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')"
  shows "s'=Fault f \<Longrightarrow> 
          s=Fault f \<or> 
          (\<exists>g c x.  redex c\<^sub>1 = Guard f g c \<and> s=Normal x \<and> x \<notin> g) \<or>
          (\<exists>b c1 x e.  redex c\<^sub>1 = Await b c1 e \<and> s=Normal x \<and> x \<in> b \<and> (\<Gamma>\<^sub>\<not>\<^sub>a)\<turnstile>\<langle>c1,s\<rangle>\<Rightarrow>s')"
using step 
by induct auto

lemma step_not_Fault_f_end:
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')"
  shows "s'\<notin> Fault ` f \<Longrightarrow> s \<notin> Fault ` f"
using step 
by induct auto

  

inductive 
      "step_ce"::"[('s,'p,'f,'e) body,('s,'p,'f,'e) config,('s,'p,'f,'e) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sub>c\<^sub>e/ _)" [81,81,81] 100)  
  for \<Gamma>::"('s,'p,'f,'e) body"
where
c_step: "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow> cf1 \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sub>c\<^sub>e cf1 "
|e_step: "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sub>e cf1 \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sub>c\<^sub>e cf1 "

lemmas step_ce_induct = step_ce.induct [of _ "(c,s)" "(c',s')", split_format (complete), case_names
c_step e_step, induct set]


inductive_cases step_ce_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sub>c\<^sub>e cf1"


lemma step_c_normal_normal: assumes a1: "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow> cf1"
      shows "\<And> c\<^sub>1 s s'. \<lbrakk>cf0 = (c\<^sub>1,Normal s);cf1=(c\<^sub>1,s');(\<forall>sa. \<not>(s'=Normal sa))\<rbrakk>
          \<Longrightarrow> P"
using a1 
by (induct rule: stepc.induct, induct, auto)

lemma normal_not_normal_eq_p: 
  assumes a1: "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sub>c\<^sub>e cf1"
  shows "\<And> c\<^sub>1 s s'. \<lbrakk>cf0 = (c\<^sub>1,Normal s);cf1=(c\<^sub>1,s');(\<forall>sa. \<not>(s'=Normal sa))\<rbrakk>
          \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sub>e cf1 \<and> \<not>( \<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow> cf1)"
by (meson step_c_normal_normal step_e.intros)

lemma call_not_normal_skip_always:
  assumes a0:"\<Gamma>\<turnstile>\<^sub>c(Call p,s) \<rightarrow> (p1,s1)" and
          a1:"\<forall>sn. s \<noteq> Normal sn" and
          a2:"p1\<noteq>Skip"
  shows "P" 
proof(cases s)
  case Normal thus ?thesis using a1 by fastforce
next
  case Stuck 
  then have a0:"\<Gamma>\<turnstile>\<^sub>c(Call p,Stuck) \<rightarrow> (p1,s1)" using a0 by auto
  show ?thesis using  a1 a2 stepc_not_normal_elim_cases(3)[OF a0] by fastforce
next
  case (Fault f) 
  then have a0:"\<Gamma>\<turnstile>\<^sub>c(Call p,Fault f) \<rightarrow> (p1,s1)" using a0 by auto
  show ?thesis using  a1 a2 stepc_not_normal_elim_cases(2)[OF a0] by fastforce
next
  case (Abrupt a)
  then have a0:"\<Gamma>\<turnstile>\<^sub>c(Call p,Abrupt a) \<rightarrow> (p1,s1)" using a0 by auto
  show ?thesis using  a1 a2 stepc_not_normal_elim_cases(1)[OF a0] by fastforce
qed

lemma call_f_step_not_s_eq_t_false:
  assumes 
     a0:"\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow> (Q,t)" and
     a1:"(redex P = Call fn \<and> \<Gamma> fn = Some bdy \<and> s=Normal s' \<and> ~(s=t)) \<or>
         (redex P = Call fn \<and> \<Gamma> fn = Some bdy \<and> s=Normal s' \<and> s=t \<and> P=Q \<and> \<Gamma> fn \<noteq> Some (Call fn))"
  shows "False"
using a0 a1
proof (induct rule:stepc_induct)
qed(fastforce+,auto)

lemma call_f_step_ce_not_s_eq_t_env_step:
  assumes 
     a0:"\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow>\<^sub>c\<^sub>e (Q,t)" and
     a1:"(redex P = Call fn \<and> \<Gamma> fn = Some bdy \<and> s=Normal s' \<and> ~(s=t)) \<or>
         (redex P = Call fn \<and> \<Gamma> fn = Some bdy \<and> s=Normal s' \<and> s=t \<and> P=Q \<and> \<Gamma> fn \<noteq> Some (Call fn)) "
  shows "\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow>\<^sub>e (Q,t)"
proof-
  have "\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow>\<^sub>e (Q,t) \<or> \<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow> (Q,t)"
  using a0 step_ce_elim_cases by fastforce
  thus ?thesis using call_f_step_not_s_eq_t_false a1 by fastforce
qed


  
abbreviation 
 "stepce_rtrancl" :: "[('s,'p,'f,'e) body,('s,'p,'f,'e) config,('s,'p,'f,'e) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sub>c\<^sub>e\<^sup>*/ _)" [81,81,81] 100)
 where                                
  "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sub>c\<^sub>e\<^sup>* cf1 \<equiv> ((CONST step_ce \<Gamma>))\<^sup>*\<^sup>* cf0 cf1" 
  (* "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sup>* cf1 \<equiv> (CONST ((stepc \<Gamma>) \<union> (step_e \<Gamma>)))\<^sup>*\<^sup>* cf0 cf1" *)

abbreviation 
 "stepce_trancl" :: "[('s,'p,'f,'e) body,('s,'p,'f,'e) config,('s,'p,'f,'e) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sub>c\<^sub>e\<^sup>+/ _)" [81,81,81] 100)
 where
  "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sub>c\<^sub>e\<^sup>+ cf1 \<equiv> (CONST step_ce \<Gamma>)\<^sup>+\<^sup>+ cf0 cf1"

subsection {*Parallel Computation: @{text "\<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sub>p  (c', s')"}*}
type_synonym ('s,'p,'f,'e) par_Simpl = "('s,'p,'f,'e)com  list" 
type_synonym ('s,'p,'f,'e) par_config = "('s,'p,'f,'e) par_Simpl \<times> ('s,'f) xstate"

definition final_c:: "('s,'p,'f,'e) par_config \<Rightarrow> bool" where
"final_c cfg = (\<forall>i. i<length (fst cfg) \<longrightarrow> final ((fst cfg)!i, snd cfg))"

inductive 
      "step_pe"::"[('s,'p,'f,'e) body,('s,'p,'f,'e) par_config,('s,'p,'f,'e) par_config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>p (_ \<rightarrow>\<^sub>e/ _)" [81,81,81] 100)  
  for \<Gamma>::"('s,'p,'f,'e) body"
where
ParEnv: "\<Gamma>\<turnstile>\<^sub>p (Ps, Normal s) \<rightarrow>\<^sub>e (Ps, Normal t)"




lemma ptranE: "\<Gamma>\<turnstile>\<^sub>p c \<rightarrow>\<^sub>e c' \<Longrightarrow> (\<And>P s t. c = (P, s) \<Longrightarrow> c' = (P, t) \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (induct c, induct c', erule  step_pe.cases, blast)

inductive_cases step_pe_Normal_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>p(PS,Normal s) \<rightarrow>\<^sub>e (Ps,t)"

inductive_cases step_pe_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>p(PS,s) \<rightarrow>\<^sub>e (Ps,t)"

inductive_cases step_pe_not_norm_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>p(Ps,s) \<rightarrow>\<^sub>e (Ps,Abrupt t)"
 "\<Gamma>\<turnstile>\<^sub>p(Ps,s) \<rightarrow>\<^sub>e (Ps,Stuck)"
 "\<Gamma>\<turnstile>\<^sub>p(Ps,s) \<rightarrow>\<^sub>e (Ps,Fault t)"

lemma env_pe_c_c'_false:
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>p (c, s) \<rightarrow>\<^sub>e (c', s')" 
   shows "~(c=c')  \<Longrightarrow> P"
using step_m ptranE by blast

lemma env_pe_c_c':
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>p (c, s) \<rightarrow>\<^sub>e (c', s')" 
   shows "(c=c')"
using env_pe_c_c'_false step_m by fastforce 

lemma env_pe_normal_s:
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>p (c, s) \<rightarrow>\<^sub>e (c', s') \<and> s\<noteq>s'" 
   shows "\<exists>sa. s = Normal sa"
using prod.inject step_pe.cases step_m by fastforce

lemma env_pe_not_normal_s:
   assumes a1:"\<Gamma>\<turnstile>\<^sub>p (c, s) \<rightarrow>\<^sub>e (c', s')" and  a2:"(\<forall>t. s\<noteq>Normal t)" 
   shows "s=s'"
using a1 a2
by (cases rule:step_pe.cases,auto) 

lemma env_pe_not_normal_s_not_norma_t:
   assumes a1:"\<Gamma>\<turnstile>\<^sub>p (c, s) \<rightarrow>\<^sub>e (c', s')" and  a2:"(\<forall>t. s\<noteq>Normal t)" 
   shows "(\<forall>t. s'\<noteq>Normal t)"
using a1 a2 env_pe_not_normal_s
by blast


inductive       
"step_p"::"[('s,'p,'f,'e) body, ('s,'p,'f,'e) par_config, 
            ('s,'p,'f,'e) par_config] \<Rightarrow> bool"
("_\<turnstile>\<^sub>p (_ \<rightarrow>/ _)" [81,81,81] 100)  
where
 ParComp: "\<lbrakk>i<length Ps;  \<Gamma>\<turnstile>\<^sub>c(Ps!i,s) \<rightarrow> (r,s')\<rbrakk> \<Longrightarrow>  
           \<Gamma>\<turnstile>\<^sub>p(Ps, s) \<rightarrow> (Ps[i:=r], s')"

lemmas steppe_induct = step_p.induct [of _ "(c,s)" "(c',s')", split_format (complete), case_names
ParComp, induct set]

inductive_cases step_p_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>p(Ps, s) \<rightarrow> u"

inductive_cases step_p_pair_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>p(Ps, s) \<rightarrow> (Qs, t)"

inductive_cases step_p_Normal_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>p(Ps, Normal s) \<rightarrow> u"


lemma par_ctranE: "\<Gamma> \<turnstile>\<^sub>p c \<rightarrow> c' \<Longrightarrow>
  (\<And>i Ps s r t. c = (Ps, s) \<Longrightarrow> c' = (Ps[i := r], t) \<Longrightarrow> i < length Ps \<Longrightarrow>
     \<Gamma> \<turnstile>\<^sub>c (Ps!i, s) \<rightarrow> (r, t) \<Longrightarrow> P) \<Longrightarrow> P"
by (induct c, induct c', erule step_p.cases, blast)

subsection \<open>Computations\<close>
subsubsection \<open>Sequential computations\<close>

type_synonym ('s,'p,'f,'e) confs = 
  "('s,'p,'f,'e) body \<times>(('s,'p,'f,'e) config) list"

inductive_set cptn :: "(('s,'p,'f,'e) confs) set"
where
  CptnOne: " (\<Gamma>, [(P,s)]) \<in> cptn"
| CptnEnv: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow>\<^sub>e (P,t); (\<Gamma>,(P, t)#xs) \<in> cptn \<rbrakk> \<Longrightarrow>
             (\<Gamma>,(P,s)#(P,t)#xs) \<in> cptn"
| CptnComp: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow> (Q,t); (\<Gamma>,(Q, t)#xs) \<in> cptn \<rbrakk> \<Longrightarrow> 
              (\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptn"

inductive_cases cptn_elim_cases [cases set]:
"(\<Gamma>, [(P,s)]) \<in> cptn"
"(\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptn"
"(\<Gamma>,(P,s)#(P,t)#xs) \<in> cptn"

inductive_cases cptn_elim_cases_pair [cases set]:
"(\<Gamma>, [x]) \<in> cptn"
"(\<Gamma>, x#x1#xs) \<in> cptn"

lemma cptn_dest:"(\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptn \<Longrightarrow> (\<Gamma>,(Q,t)#xs)\<in> cptn"
by (auto dest: cptn_elim_cases)

lemma cptn_dest_pair:"(\<Gamma>,x#x1#xs) \<in> cptn \<Longrightarrow> (\<Gamma>,x1#xs)\<in> cptn"
proof -
  assume "(\<Gamma>,x#x1#xs) \<in> cptn"
  thus ?thesis using cptn_dest prod.collapse by metis
qed

lemma cptn_dest1:"(\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptn \<Longrightarrow> (\<Gamma>,(P,s)#[(Q,t)])\<in> cptn"
proof -
  assume a1: "(\<Gamma>, (P, s) # (Q, t) # xs) \<in> cptn"
  have "(\<Gamma>, [(Q, t)]) \<in> cptn"
    by (meson cptn.CptnOne)
  thus ?thesis       
  proof (cases s)
    case (Normal s') 
     then have f1: "(\<Gamma>, (P, Normal s') # (Q, t) # xs) \<in> cptn"
       using Normal a1 by blast
     have "(\<Gamma>, [(P, t)]) \<in> cptn \<longrightarrow> (\<Gamma>, [(P, Normal s'), (P, t)]) \<in> cptn"
       by (simp add: Env cptn.CptnEnv)       
     thus ?thesis
      using f1 by (metis (no_types) Normal `(\<Gamma>, [(Q, t)]) \<in> cptn` cptn.CptnComp cptn_elim_cases(2))
  next
    case (Abrupt x) thus ?thesis  
     using `(\<Gamma>, [(Q, t)]) \<in> cptn` a1 cptn.CptnComp cptn_elim_cases(2) CptnEnv by metis
  next
    case (Stuck) thus ?thesis 
     using `(\<Gamma>, [(Q, t)]) \<in> cptn` a1 cptn.CptnComp cptn_elim_cases(2) CptnEnv by metis
  next 
    case (Fault f) thus ?thesis
     using `(\<Gamma>, [(Q, t)]) \<in> cptn` a1 cptn.CptnComp cptn_elim_cases(2) CptnEnv by metis
  qed
qed

lemma cptn_dest1_pair:"(\<Gamma>,x#x1#xs) \<in> cptn \<Longrightarrow> (\<Gamma>,x#[x1])\<in> cptn"
proof -
  assume "(\<Gamma>,x#x1#xs) \<in> cptn"
  thus ?thesis using cptn_dest1 prod.collapse by metis
qed

lemma cptn_append_is_cptn [rule_format]: 
 "\<forall>b a. (\<Gamma>,b#c1)\<in>cptn \<longrightarrow>  (\<Gamma>,a#c2)\<in>cptn \<longrightarrow> (b#c1)!length c1=a \<longrightarrow> (\<Gamma>,b#c1@c2)\<in>cptn"
apply(induct c1)
 apply simp
apply clarify
apply(erule cptn.cases,simp_all)
apply (simp add: cptn.CptnEnv)
by (simp add: cptn.CptnComp)

lemma cptn_dest_2:
  "(\<Gamma>,a#xs@ys) \<in> cptn  \<Longrightarrow> (\<Gamma>,a#xs)\<in> cptn"
proof (induct "xs" arbitrary: a)
  case Nil thus ?case using cptn.simps by fastforce 
next
  case (Cons x xs') 
  then have "(\<Gamma>,a#[x])\<in>cptn" by (simp add: cptn_dest1_pair)
  also have "(\<Gamma>, x # xs') \<in> cptn"
    using Cons.hyps Cons.prems cptn_dest_pair by fastforce    
  ultimately show ?case using cptn_append_is_cptn [of \<Gamma> a "[x]" x xs']
    by force    
qed   


lemma last_not_F:
assumes 
  a0:"(\<Gamma>,xs)\<in>cptn"  
shows "snd (last xs) \<notin> Fault ` F \<Longrightarrow> \<forall>i < length xs. snd (xs!i) \<notin> Fault ` F"
using a0
proof(induct) print_cases
  case (CptnOne \<Gamma> p s) thus ?case by auto
next
  case (CptnEnv  \<Gamma> P s t xs) 
  thus ?case using stepe_not_Fault_f_end
  proof -
  { fix nn :: nat
    have "snd (last ((P, t) # xs)) \<notin> Fault ` F"
      using CptnEnv.prems by force
    then have "\<not> nn < length ((P, s) # (P, t) # xs) \<or> snd (((P, s) # (P, t) # xs) ! nn) \<notin> Fault ` F"
      by (metis (no_types) CptnEnv.hyps(1) CptnEnv.hyps(3) length_Cons less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc snd_conv stepe_not_Fault_f_end) 
  }
  then have "\<forall>n. \<not> n < length ((P, s) # (P, t) # xs) \<or> snd (((P, s) # (P, t) # xs) ! n) \<notin> Fault ` F"
    by meson
  then show ?thesis
    by metis
  qed    
next
  case (CptnComp \<Gamma> P s Q t xs) 
  have "snd (last ((Q, t) # xs)) \<notin> Fault ` F"
    using CptnComp.prems by force
  then have all:"\<forall>i<length ((Q, t) # xs). snd (((Q, t) # xs) ! i) \<notin> Fault ` F"
    using CptnComp.hyps by force
  then have "t \<notin> Fault ` F"
    by force
  then have "s \<notin> Fault ` F" using step_not_Fault_f_end
    using CptnComp.hyps(1) by blast
  then have zero:"snd (P,s) \<notin> Fault ` F" by auto
  show ?case 
  proof -
  { fix nn :: nat
    have "\<not> nn < length ((P, s) # (Q, t) # xs) \<or> snd (((P, s) # (Q, t) # xs) ! nn) \<notin> Fault ` F"
      by (metis (no_types) \<open>\<forall>i<length ((Q, t) # xs). snd (((Q, t) # xs) ! i) \<notin> Fault ` F\<close> \<open>snd (P, s) \<notin> Fault ` F\<close> diff_Suc_1 length_Cons less_Suc_eq_0_disj nth_Cons') 
  }
  then show ?thesis
    by meson
  qed 
qed

definition cp :: "('s,'p,'f,'e) body \<Rightarrow> ('s,'p,'f,'e) com \<Rightarrow> 
                  ('s,'f) xstate \<Rightarrow> (('s,'p,'f,'e) confs) set" where
  "cp \<Gamma> P s \<equiv> {(\<Gamma>1,l). l!0=(P,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>1=\<Gamma>}"  

 

lemma cp_sub: 
  assumes a0: "(\<Gamma>,(x#l0)@l1) \<in> cp \<Gamma> P s"
  shows "(\<Gamma>,(x#l0)) \<in> cp \<Gamma> P s"
proof -
  have "(x#l0)!0 = (P,s)" using a0 unfolding cp_def by auto
  also have "(\<Gamma>,(x#l0))\<in>cptn" using a0 unfolding cp_def
  using cptn_dest_2 by fastforce
  ultimately show ?thesis using a0 unfolding cp_def by blast
qed

subsubsection \<open>Parallel computations\<close>

type_synonym ('s,'p,'f,'e) par_confs = "('s,'p,'f,'e) body \<times>(('s,'p,'f,'e) par_config) list"

inductive_set par_cptn :: "('s,'p,'f,'e) par_confs set"
where
  ParCptnOne: "(\<Gamma>, [(P,s)]) \<in> par_cptn"
| ParCptnEnv: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p(P,s) \<rightarrow>\<^sub>e (P,t);(\<Gamma>,(P, t)#xs) \<in> par_cptn \<rbrakk> \<Longrightarrow>(\<Gamma>,(P,s)#(P,t)#xs) \<in> par_cptn"
| ParCptnComp: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>p(P,s) \<rightarrow> (Q,t); (\<Gamma>,(Q,t)#xs) \<in> par_cptn \<rbrakk> \<Longrightarrow> (\<Gamma>,(P,s)#(Q,t)#xs) \<in> par_cptn"

inductive_cases par_cptn_elim_cases [cases set]:
"(\<Gamma>, [(P,s)]) \<in> par_cptn"
"(\<Gamma>,(P,s)#(Q,t)#xs) \<in> par_cptn"

lemma pe_ce: 
  assumes a1:"\<Gamma>\<turnstile>\<^sub>p(P,s) \<rightarrow>\<^sub>e (P,t)"
  shows "\<forall>i<length P. \<Gamma>\<turnstile>\<^sub>c(P!i,s) \<rightarrow>\<^sub>e (P!i,t)"
proof -
  {fix i
   assume "i< length P"
   have "\<Gamma>\<turnstile>\<^sub>c(P!i,s) \<rightarrow>\<^sub>e (P!i,t)" using a1
  by (metis Env Env_n env_pe_not_normal_s)
  }
  thus "\<forall>i<length P. \<Gamma>\<turnstile>\<^sub>c(P!i,s) \<rightarrow>\<^sub>e (P!i,t)" by blast
qed

type_synonym ('s,'p,'f,'e) par_com = "('s,'p,'f,'e) com list"

definition par_cp :: "('s,'p,'f,'e) body \<Rightarrow> ('s,'p,'f,'e) com list \<Rightarrow> ('s,'f) xstate \<Rightarrow> (('s,'p,'f,'e) par_confs) set" 
where
  "par_cp \<Gamma> P s \<equiv> {(\<Gamma>1,l). l!0=(P,s) \<and> (\<Gamma>,l) \<in> par_cptn \<and> \<Gamma>1=\<Gamma>}"  

(* definition par_cp :: "('s,'p,'f,'e) body \<Rightarrow> ('s,'p,'f,'e) com list \<Rightarrow> ('s,'f) xstate \<Rightarrow> (('s,'p,'f,'e) par_confs) set" 
where
  "par_cp \<Gamma> P s \<equiv> {(\<Gamma>1,l). l!0=(P,s) \<and> (\<Gamma>,l) \<in> par_cptn \<and> \<Gamma>1=\<Gamma>}" *)

lemma par_cptn_dest:"(\<Gamma>,(P,s)#(Q,t)#xs) \<in> par_cptn \<Longrightarrow> (\<Gamma>,(Q,t)#xs)\<in> par_cptn"
by (auto dest: par_cptn_elim_cases)


text {*
lemmas about single step computation
*}


(* ************************************************************************ *)
subsection {* Structural Properties of Small Step Computations *}
(* ************************************************************************ *)
lemma redex_not_Seq: "redex c = Seq c1 c2 \<Longrightarrow> P"
  apply (induct c)
  apply auto
  done
lemma redex_not_Catch: "redex c = Catch c1 c2 \<Longrightarrow> P"
  apply (induct c)
  apply auto
  done

lemma no_step_final: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c(c,s) \<rightarrow> (c',s')"
  shows "final (c,s) \<Longrightarrow> P"
using step
by induct (auto simp add: final_def)


lemma no_step_final':
  assumes step: "\<Gamma>\<turnstile>\<^sub>c cfg \<rightarrow> cfg'"
  shows "final cfg \<Longrightarrow> P"
using step
  by (cases cfg, cases cfg') (auto intro: no_step_final)


lemma step_Abrupt:
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', s')"
  shows "\<And>x. s=Abrupt x \<Longrightarrow> s'=Abrupt x"
using step
by (induct) auto

lemma step_Fault: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', s')"
  shows "\<And>f. s=Fault f \<Longrightarrow> s'=Fault f"
using step
by (induct) auto

lemma step_Stuck: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', s')"
  shows "\<And>f. s=Stuck \<Longrightarrow> s'=Stuck"
using step
by (induct) auto

lemma step_not_normal_not_normal:
  assumes step:"\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', s')"
  shows "\<forall>s1. s\<noteq>Normal s1 \<Longrightarrow> \<forall>s1. s' \<noteq> Normal s1"
using step step_Abrupt step_Stuck step_Fault
by (induct) auto

lemma step_not_normal_s_eq_t:
  assumes step:"\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', t)"
  shows "\<forall>s1. s\<noteq>Normal s1 \<Longrightarrow> s=t"
using step step_Abrupt step_Stuck step_Fault
by (induct) auto

lemma ce_not_normal_s:
   assumes a1:"\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sub>c\<^sub>e cf1"
   shows "\<And> c\<^sub>1 c\<^sub>2 s s'. \<lbrakk>cf0 = (c\<^sub>1,s);cf1=(c\<^sub>2,s');(\<forall>sa. (s\<noteq>Normal sa))\<rbrakk>
                     \<Longrightarrow> s=s'"
using a1
apply (clarify, cases rule:step_ce.cases)
by (metis step_not_normal_s_eq_t env_not_normal_s)+

lemma SeqSteps: 
  assumes steps: "\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1\<rightarrow>\<^sup>* cfg\<^sub>2"
  shows "\<And> c\<^sub>1 s c\<^sub>1' s'. \<lbrakk>cfg\<^sub>1 = (c\<^sub>1,s);cfg\<^sub>2=(c\<^sub>1',s')\<rbrakk>
          \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow>\<^sup>* (Seq c\<^sub>1' c\<^sub>2, s')"
using steps
proof (induct rule: converse_rtranclp_induct [case_names Refl Trans]) 
  case Refl
  thus ?case
    by simp
next
  case (Trans cfg\<^sub>1 cfg'')      
  have step: "\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow> cfg''" using Trans.hyps(1) by blast
  have steps: "\<Gamma>\<turnstile>\<^sub>c cfg'' \<rightarrow>\<^sup>* cfg\<^sub>2" by fact
  have cfg\<^sub>1: "cfg\<^sub>1 = (c\<^sub>1, s)" and cfg\<^sub>2: "cfg\<^sub>2 = (c\<^sub>1', s')"  by fact+
  obtain c\<^sub>1'' s'' where cfg'': "cfg''=(c\<^sub>1'',s'')"
    by (cases cfg'') auto
  from step cfg\<^sub>1 cfg'' 
  have "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1,s) \<rightarrow> (c\<^sub>1'',s'')"
    by simp  
  hence "\<Gamma>\<turnstile>\<^sub>c (Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Seq c\<^sub>1'' c\<^sub>2,s'')" by (simp add: Seqc)    
  also from Trans.hyps (3) [OF cfg'' cfg\<^sub>2]
  have "\<Gamma>\<turnstile>\<^sub>c (Seq c\<^sub>1'' c\<^sub>2, s'') \<rightarrow>\<^sup>* (Seq c\<^sub>1' c\<^sub>2, s')" .
  finally show ?case .
qed

lemma CatchSteps: 
  assumes steps: "\<Gamma>\<turnstile>\<^sub>ccfg\<^sub>1\<rightarrow>\<^sup>* cfg\<^sub>2"
  shows "\<And> c\<^sub>1 s c\<^sub>1' s'. \<lbrakk>cfg\<^sub>1 = (c\<^sub>1,s); cfg\<^sub>2=(c\<^sub>1',s')\<rbrakk>
          \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow>\<^sup>* (Catch c\<^sub>1' c\<^sub>2, s')"
using steps
proof (induct rule: converse_rtranclp_induct [case_names Refl Trans])
  case Refl
  thus ?case
    by simp
next
  case (Trans cfg\<^sub>1 cfg'')
  have step: "\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow> cfg''" by fact
  have steps: "\<Gamma>\<turnstile>\<^sub>c cfg'' \<rightarrow>\<^sup>* cfg\<^sub>2" by fact
  have cfg\<^sub>1: "cfg\<^sub>1 = (c\<^sub>1, s)" and cfg\<^sub>2: "cfg\<^sub>2 = (c\<^sub>1', s')"  by fact+
  obtain c\<^sub>1'' s'' where cfg'': "cfg''=(c\<^sub>1'',s'')"
    by (cases cfg'') auto
  from step cfg\<^sub>1 cfg'' 
  have s: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1,s) \<rightarrow> (c\<^sub>1'',s'')"
    by simp
  hence "\<Gamma>\<turnstile>\<^sub>c (Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Catch c\<^sub>1'' c\<^sub>2,s'')"
    by (rule stepc.Catchc)
  also from Trans.hyps (3) [OF cfg'' cfg\<^sub>2]
  have "\<Gamma>\<turnstile>\<^sub>c (Catch c\<^sub>1'' c\<^sub>2, s'') \<rightarrow>\<^sup>* (Catch c\<^sub>1' c\<^sub>2, s')" .
  finally show ?case .      
qed

lemma steps_Fault: "\<Gamma>\<turnstile>\<^sub>c (c, Fault f) \<rightarrow>\<^sup>* (Skip, Fault f)"
proof (induct c)
  case (Seq c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, Fault f) \<rightarrow>\<^sup>* (Skip, Fault f)" by fact
  have steps_c\<^sub>2: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>2, Fault f) \<rightarrow>\<^sup>* (Skip, Fault f)" by fact
  from SeqSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma>\<turnstile>\<^sub>c (Seq c\<^sub>1 c\<^sub>2, Fault f) \<rightarrow>\<^sup>* (Seq Skip c\<^sub>2, Fault f)".
  also
  have "\<Gamma>\<turnstile>\<^sub>c (Seq Skip c\<^sub>2, Fault f) \<rightarrow> (c\<^sub>2, Fault f)" by (rule SeqSkipc)
  also note steps_c\<^sub>2
  finally show ?case by simp
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, Fault f) \<rightarrow>\<^sup>* (Skip, Fault f)" by fact
  from CatchSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma>\<turnstile>\<^sub>c (Catch c\<^sub>1 c\<^sub>2, Fault f) \<rightarrow>\<^sup>* (Catch Skip c\<^sub>2, Fault f)".
  also
  have "\<Gamma>\<turnstile>\<^sub>c (Catch Skip c\<^sub>2, Fault f) \<rightarrow> (Skip, Fault f)" by (rule CatchSkipc) 
  finally show ?case by simp
qed (fastforce intro: stepc.intros)+


lemma steps_Stuck: "\<Gamma>\<turnstile>\<^sub>c (c, Stuck) \<rightarrow>\<^sup>* (Skip, Stuck)"
proof (induct c)
  case (Seq c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, Stuck) \<rightarrow>\<^sup>* (Skip, Stuck)" by fact
  have steps_c\<^sub>2: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>2, Stuck) \<rightarrow>\<^sup>* (Skip, Stuck)" by fact
  from SeqSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma>\<turnstile>\<^sub>c (Seq c\<^sub>1 c\<^sub>2, Stuck) \<rightarrow>\<^sup>* (Seq Skip c\<^sub>2, Stuck)".
  also
  have "\<Gamma>\<turnstile>\<^sub>c (Seq Skip c\<^sub>2, Stuck) \<rightarrow> (c\<^sub>2, Stuck)" by (rule SeqSkipc)
  also note steps_c\<^sub>2
  finally show ?case by simp
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, Stuck) \<rightarrow>\<^sup>* (Skip, Stuck)" by fact
  from CatchSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma>\<turnstile>\<^sub>c (Catch c\<^sub>1 c\<^sub>2, Stuck) \<rightarrow>\<^sup>* (Catch Skip c\<^sub>2, Stuck)" .
  also
  have "\<Gamma>\<turnstile>\<^sub>c (Catch Skip c\<^sub>2, Stuck) \<rightarrow> (Skip, Stuck)" by (rule CatchSkipc) 
  finally show ?case by simp
qed (fastforce intro: stepc.intros)+

lemma steps_Abrupt: "\<Gamma>\<turnstile>\<^sub>c (c, Abrupt s) \<rightarrow>\<^sup>* (Skip, Abrupt s)"
proof (induct c)
  case (Seq c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, Abrupt s) \<rightarrow>\<^sup>* (Skip, Abrupt s)" by fact
  have steps_c\<^sub>2: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>2, Abrupt s) \<rightarrow>\<^sup>* (Skip, Abrupt s)" by fact
  from SeqSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma>\<turnstile>\<^sub>c (Seq c\<^sub>1 c\<^sub>2, Abrupt s) \<rightarrow>\<^sup>* (Seq Skip c\<^sub>2, Abrupt s)".
  also
  have "\<Gamma>\<turnstile>\<^sub>c (Seq Skip c\<^sub>2, Abrupt s) \<rightarrow> (c\<^sub>2, Abrupt s)" by (rule SeqSkipc)
  also note steps_c\<^sub>2
  finally show ?case by simp
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, Abrupt s) \<rightarrow>\<^sup>* (Skip, Abrupt s)" by fact
  from CatchSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma>\<turnstile>\<^sub>c (Catch c\<^sub>1 c\<^sub>2, Abrupt s) \<rightarrow>\<^sup>* (Catch Skip c\<^sub>2, Abrupt s)".
  also
  have "\<Gamma>\<turnstile>\<^sub>c (Catch Skip c\<^sub>2, Abrupt s) \<rightarrow> (Skip, Abrupt s)" by (rule CatchSkipc) 
  finally show ?case by simp
qed (fastforce intro: stepc.intros)+

lemma step_Fault_prop: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', s')"
  shows "\<And>f. s=Fault f \<Longrightarrow> s'=Fault f"
using step
by (induct) auto

lemma step_Abrupt_prop: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', s')"
  shows "\<And>x. s=Abrupt x \<Longrightarrow> s'=Abrupt x"
using step
by (induct) auto

lemma step_Stuck_prop: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', s')"
  shows "s=Stuck \<Longrightarrow> s'=Stuck"
using step
by (induct) auto

lemma steps_Fault_prop: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sup>* (c', s')"
  shows "s=Fault f \<Longrightarrow> s'=Fault f"
using step
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case by simp
next
  case (Trans c s c'' s'')
  thus ?case by (simp add: step_Fault_prop)    
qed

lemma steps_Abrupt_prop: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sup>* (c', s')"
  shows "s=Abrupt t \<Longrightarrow> s'=Abrupt t"
using step
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case by simp
next
  case (Trans c s c'' s'')
  thus ?case
    by (auto intro: step_Abrupt_prop)
qed

lemma steps_Stuck_prop: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sup>* (c', s')"
  shows "s=Stuck \<Longrightarrow> s'=Stuck"
using step
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case by simp   
next
  case (Trans c s c'' s'')
  thus ?case
    by (auto intro: step_Stuck_prop)
qed

lemma step_seq_throw_normal:
assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', s')" and
        c_val: "c=Seq Throw Q \<and> c'=Throw"
shows "\<exists>sa. s=Normal sa"
using step c_val
proof (cases s)
  case Normal 
  thus "\<exists>sa. s=Normal sa" by auto
next
  case Abrupt
  thus "\<exists>sa. s=Normal sa" using step c_val stepc_elim_cases(5)[of \<Gamma> Throw Q s "(Throw,s')"] by auto 
next 
  case Stuck
  thus "\<exists>sa. s=Normal sa" using step c_val stepc_elim_cases(5)[of \<Gamma> Throw Q s "(Throw,s')"] by auto
next
  case Fault
    thus "\<exists>sa. s=Normal sa" using step c_val stepc_elim_cases(5)[of \<Gamma> Throw Q s "(Throw,s')"] by auto
qed


lemma step_catch_throw_normal:
assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', s')" and
        c_val: "c=Catch Throw Q \<and> c'=Throw"
shows "\<exists>sa. s=Normal sa"
using step c_val
proof (cases s)
  case Normal 
  thus "\<exists>sa. s=Normal sa" by auto
next
  case Abrupt
  thus "\<exists>sa. s=Normal sa" using step c_val stepc_elim_cases(12)[of \<Gamma> Throw Q s "(Throw,s')"] by auto 
next 
  case Stuck
  thus "\<exists>sa. s=Normal sa" using step c_val stepc_elim_cases(12)[of \<Gamma> Throw Q s "(Throw,s')"] by auto
next
  case Fault
    thus "\<exists>sa. s=Normal sa" using step c_val stepc_elim_cases(12)[of \<Gamma> Throw Q s "(Throw,s')"] by auto
qed

lemma step_normal_to_normal[rule_format]:
assumes step:"\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sup>* (c', s')" and
        sn: "s = Normal sa" and
        finalc':"(\<Gamma>\<turnstile>\<^sub>c (c', s') \<rightarrow>\<^sup>*(c1, s1) \<and>  (\<exists>sb. s1 = Normal sb))"
shows " (\<exists>sc. s'=Normal sc)"
using step sn finalc'                                  
 proof (induct arbitrary: sa rule: converse_rtranclp_induct2 [case_names Refl Trans])
   case Refl show ?case by (simp add: Refl.prems)              
 next     
   case (Trans c s c'' s'') thm converse_rtranclpE2 
     thus ?case
     proof (cases s'')  
      case (Abrupt a1) thus ?thesis using finalc' by (metis steps_Abrupt_prop Trans.hyps(2))                
     next
      case Stuck thus ?thesis using finalc' by (metis steps_Stuck_prop Trans.hyps(2))          
     next
      case Fault thus ?thesis using finalc' by (metis steps_Fault_prop Trans.hyps(2))        
     next 
      case Normal thus ?thesis using Trans.hyps(3) finalc' by blast 
    qed 
qed

lemma step_spec_skip_normal_normal:
  assumes a0:"\<Gamma>\<turnstile>\<^sub>c (c,s)  \<rightarrow> (c',s')" and
          a1:"c=Spec r e" and
          a2: "s=Normal s1" and
          a3: "c'=Skip" and
          a4: "(\<exists>t. (s1,t) \<in> r)"
  shows "\<exists>s1'. s'=Normal s1'"
proof (cases s')  
  case (Normal u) thus ?thesis by auto
next
  case Stuck 
    have "\<forall>f r b p e. \<not> f\<turnstile>\<^sub>c (LanguageCon.com.Spec r e, Normal b) \<rightarrow> p \<or> 
            (\<exists>ba. p = (Skip::('b, 'a, 'c,'d) com, Normal ba) \<and> (b, ba) \<in> r) \<or> 
            p = (Skip, Stuck) \<and> (\<forall>ba. (b, ba) \<notin> r)"
      by (meson stepc_Normal_elim_cases(4))
      thus ?thesis using a0 a1 a2 a4 by blast
next
  case (Fault f) 
  have "\<forall>f r b p e. \<not> f\<turnstile>\<^sub>c (LanguageCon.com.Spec r e, Normal b) \<rightarrow> p \<or> 
            (\<exists>ba. p = (Skip::('b, 'a, 'c,'d) com, Normal ba) \<and> (b, ba) \<in> r) \<or> 
            p = (Skip, Stuck) \<and> (\<forall>ba. (b, ba) \<notin> r)"
    by (meson stepc_Normal_elim_cases(4))
    thus ?thesis using a0 a1 a2 a4 by blast                       
next
  have "\<forall>f r b p e. \<not> f\<turnstile>\<^sub>c (LanguageCon.com.Spec r e, Normal b) \<rightarrow> p \<or> 
        (\<exists>ba. p = (Skip::('b, 'a, 'c,'d) com, Normal ba) \<and> (b, ba) \<in> r) \<or> 
        p = (Skip, Stuck) \<and> (\<forall>ba. (b, ba) \<notin> r)"
    by (meson stepc_Normal_elim_cases(4))
    thus ?thesis using a0 a1 a2 a4 by blast
qed


text{* if not Normal not environmental *}

(* 

NOTE
Call always change the program now 

lemma no_advance_call_inf:
assumes a0: "redex p1 = Call f" and
        a1: "(\<Gamma> f) = Some (Call f)" 
shows "\<Gamma>\<turnstile>\<^sub>c (p1,Normal s) \<rightarrow> (p1, Normal s)"
using a0 a1
proof (induct p1)
  case (Catch) thus ?case by (simp add: Catchc)
next
  case (Seq) thus ?case by (simp add: Seqc)
next
  case (Call) thus ?case
    by (simp add: Callc) 
qed(auto) *)

lemma no_advance_seq:
assumes a0: "P = Seq p1 p2" and
        a1: "\<Gamma>\<turnstile>\<^sub>c (p1,Normal s) \<rightarrow> (p1, Normal s)"
shows "\<Gamma>\<turnstile>\<^sub>c (P,Normal s) \<rightarrow> (P, Normal s)"
by (simp add: Seqc a0 a1)

lemma no_advance_catch:
assumes a0: "P = Catch p1 p2" and
        a1: "\<Gamma>\<turnstile>\<^sub>c (p1,Normal s) \<rightarrow> (p1, Normal s)"
shows "\<Gamma>\<turnstile>\<^sub>c (P,Normal s) \<rightarrow> (P, Normal s)"
by (simp add: Catchc a0 a1)

lemma not_step_c_env: 
"\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c, s') \<Longrightarrow> 
 (\<And>sa. \<not>(s=Normal sa)) \<Longrightarrow> 
  (\<And>sa. \<not>(s'=Normal sa))"
by (fastforce elim:stepe_elim_cases)

lemma step_c_env_not_normal_eq_state: 
"\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c, s') \<Longrightarrow> 
 (\<And>sa. \<not>(s=Normal sa)) \<Longrightarrow> 
  s=s'"
by (fastforce elim:stepe_elim_cases)

lemma not_eq_not_env:
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e (c', s')" 
   shows "~(c=c') \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', s') \<Longrightarrow> P"
using step_m etranE by blast


lemma step_ce_not_step_e_step_c:
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e (c', s')" 
   shows "\<not> (\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', s')) \<Longrightarrow>(\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', s'))"
using step_m  step_ce_elim_cases by blast

lemma step_ce_notNormal:   
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e (c', s')" 
   shows "(\<forall>sa. \<not>(s=Normal sa)) \<Longrightarrow> s'=s"
using step_m
proof (induct rule:step_ce_induct) 
  case (e_step a b a' b')
  have "\<forall>f p pa. \<not> f\<turnstile>\<^sub>c p \<rightarrow>\<^sub>e pa \<or> (\<exists>c. (\<exists>x. p = (c::('b, 'a, 'c,'d) LanguageCon.com, x)) \<and> (\<exists>x. pa = (c, x)))"
    by (fastforce elim:etranE stepe_elim_cases)
  thus ?case
    using stepe_elim_cases e_step.hyps e_step.prems by blast
next
  case (c_step a b a' b')
  thus ?case 
  proof (cases b)
    case (Normal) thus ?thesis using c_step.prems by auto   
  next
    case (Stuck) thus ?thesis  
      using SmallStepCon.step_Stuck_prop c_step.hyps by blast 
  next
    case (Fault f) thus ?thesis 
     using SmallStepCon.step_Fault_prop c_step.hyps by fastforce
  next
    case (Abrupt a) thus ?thesis
      using SmallStepCon.step_Abrupt_prop c_step.hyps by fastforce 
  qed
qed

lemma steps_ce_not_Normal:  
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (c', s')" 
   shows "\<forall>sa. \<not>(s=Normal sa) \<Longrightarrow> s'=s"
using step_m
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl then show ?case by auto
next
  case (Trans a b a' b') 
  thus ?case using step_ce_notNormal by blast 
qed

lemma steps_not_normal_ce_c: 
  assumes steps: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (c', s')"
  shows         "( \<forall>sa. \<not>(s=Normal sa)) \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sup>* (c', s')"
using steps
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case by auto
next
  case (Trans a b a' b') 
    then have "b=b'" using step_ce_notNormal by blast
    then have "\<Gamma>\<turnstile>\<^sub>c (a', b') \<rightarrow>\<^sup>* (c', s')" using `b=b'` Trans.hyps(3) Trans.prems by blast
    then have "\<Gamma>\<turnstile>\<^sub>c (a, b) \<rightarrow> (a', b') \<or> \<Gamma>\<turnstile>\<^sub>c (a, b) \<rightarrow>\<^sub>e (a', b')"
      using Trans.hyps(1) by (fastforce elim: step_ce_elim_cases)
    thus ?case
    proof
      assume "\<Gamma>\<turnstile>\<^sub>c (a, b) \<rightarrow> (a', b')" 
      thus ?thesis using `\<Gamma>\<turnstile>\<^sub>c (a', b') \<rightarrow>\<^sup>* (c', s')` by auto 
    next
      assume "\<Gamma>\<turnstile>\<^sub>c (a, b) \<rightarrow>\<^sub>e (a', b')"   
       have "a = a'"
         by (meson Trans.hyps(1) `\<Gamma>\<turnstile>\<^sub>c (a, b) \<rightarrow>\<^sub>e (a', b')` not_eq_not_env)   
         thus ?thesis using `\<Gamma>\<turnstile>\<^sub>c (a', b') \<rightarrow>\<^sup>* (c', s')` `b = b'` by force           
    qed
qed

lemma steps_c_ce: 
  assumes steps: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sup>* (c', s')"
  shows         "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (c', s')"
using steps
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case by auto
next
  case (Trans a b a' b') 
  have "\<Gamma>\<turnstile>\<^sub>c (a, b) \<rightarrow>\<^sub>c\<^sub>e (a', b')"
    using Trans.hyps(1) c_step by blast
  thus ?case
    by (simp add: Trans.hyps(3) converse_rtranclp_into_rtranclp)
qed

lemma steps_not_normal_c_ce: 
  assumes steps: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sup>* (c', s')"
  shows         "( \<forall>sa. \<not>(s=Normal sa)) \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (c', s')"
by (simp add: steps steps_c_ce)

lemma steps_not_normal_c_eq_ce:
assumes normal: "( \<forall>sa. \<not>(s=Normal sa))"
shows         " \<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sup>* (c', s') =  \<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (c', s')"
using normal
using steps_c_ce steps_not_normal_ce_c by auto 

lemma steps_ce_Fault: "\<Gamma>\<turnstile>\<^sub>c (c, Fault f) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (Skip, Fault f)"
by (simp add: SmallStepCon.steps_Fault steps_c_ce)

lemma steps_ce_Stuck: "\<Gamma>\<turnstile>\<^sub>c (c, Stuck) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (Skip, Stuck)"
by (simp add: SmallStepCon.steps_Stuck steps_c_ce)

lemma steps_ce_Abrupt: "\<Gamma>\<turnstile>\<^sub>c (c, Abrupt a) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (Skip, Abrupt a)"
by (simp add: SmallStepCon.steps_Abrupt steps_c_ce)

lemma step_ce_seq_throw_normal:
assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e (c', s')" and
        c_val: "c=Seq Throw Q \<and> c'=Throw"
shows "\<exists>sa. s=Normal sa"
using step c_val not_eq_not_env 
      step_ce_not_step_e_step_c step_seq_throw_normal by blast

lemma step_ce_catch_throw_normal:
assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e (c', s')" and
        c_val: "c=Catch Throw Q \<and> c'=Throw"
shows "\<exists>sa. s=Normal sa"
using step c_val not_eq_not_env
      step_ce_not_step_e_step_c step_catch_throw_normal  by blast 

lemma step_ce_normal_to_normal[rule_format]:
assumes step:"\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (c', s')" and
        sn: "s = Normal sa" and
        finalc':"(\<Gamma>\<turnstile>\<^sub>c (c', s') \<rightarrow>\<^sub>c\<^sub>e\<^sup>*(c1, s1) \<and>  (\<exists>sb. s1 = Normal sb))"
shows "         
       (\<exists>sc. s'=Normal sc)"
using step sn finalc' steps_ce_not_Normal by blast      

lemma SeqSteps_ce: 
  assumes steps: "\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1\<rightarrow>\<^sub>c\<^sub>e\<^sup>* cfg\<^sub>2"
  shows "\<And> c\<^sub>1 s c\<^sub>1' s'. \<lbrakk>cfg\<^sub>1 = (c\<^sub>1,s);cfg\<^sub>2=(c\<^sub>1',s')\<rbrakk>
          \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (Seq c\<^sub>1' c\<^sub>2, s')"
using steps
proof (induct rule: converse_rtranclp_induct [case_names Refl Trans]) 
  case Refl
  thus ?case
    by simp
next
  case (Trans cfg\<^sub>1 cfg'') 
  then have "\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow> cfg'' \<or> \<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow>\<^sub>e cfg''" 
   using step_ce_elim_cases by blast
  thus ?case 
  proof
    assume a1:"\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow>\<^sub>e cfg''"          
    have "\<forall>f p pa. \<not> f\<turnstile>\<^sub>c p \<rightarrow>\<^sub>e pa \<or> (\<exists>c. 
                   (\<exists>x. p = (c::('a, 'b, 'c,'d) LanguageCon.com, x)) \<and> (\<exists>x. pa = (c, x)))"
      by (meson etranE)
    then obtain cc :: "('b \<Rightarrow> ('a, 'b, 'c,'d) LanguageCon.com option) \<Rightarrow> 
                              ('a, 'b, 'c,'d) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> 
                              ('a, 'b, 'c,'d) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> 
                              ('a, 'b, 'c,'d) LanguageCon.com" and 
                xx :: "('b \<Rightarrow> ('a, 'b, 'c,'d) LanguageCon.com option) \<Rightarrow> 
                       ('a, 'b, 'c,'d) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> 
                       ('a, 'b, 'c,'d) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> ('a, 'c) xstate" and
                xxa :: "('b \<Rightarrow> ('a, 'b, 'c,'d) LanguageCon.com option) \<Rightarrow> 
                        ('a, 'b, 'c,'d) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> 
                       ('a, 'b, 'c,'d) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> ('a, 'c) xstate" where
      f1: "\<forall>f p pa. \<not> f\<turnstile>\<^sub>c p \<rightarrow>\<^sub>e pa \<or> p = (cc f p pa, xx f p pa) \<and> pa = (cc f p pa, xxa f p pa)"
      by (metis (no_types))
    have f2: "\<forall>f c x xa. \<not> f\<turnstile>\<^sub>c (c::('a, 'b, 'c,'d) LanguageCon.com, x) \<rightarrow>\<^sub>e (c, xa) \<or> 
                            (\<exists>a. x = Normal a) \<or> (\<forall>a. xa \<noteq> Normal a) \<and> x = xa"
      by (metis stepe_elim_cases)
    have f3: "(c\<^sub>1, xxa \<Gamma> cfg\<^sub>1 cfg'') = cfg''"
      using f1 by (metis Trans.prems(1) a1 fst_conv)
    hence "\<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Seq c\<^sub>1 c\<^sub>2, xxa \<Gamma> cfg\<^sub>1 cfg'') \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (LanguageCon.com.Seq c\<^sub>1' c\<^sub>2, s')"
      using Trans.hyps(3) Trans.prems(2) by force
    thus ?thesis
      using f3 f2 by (metis (no_types) Env Trans.prems(1) a1 e_step r_into_rtranclp 
                       rtranclp.rtrancl_into_rtrancl rtranclp_idemp)   
  next
     assume "\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow> cfg''"
     thus ?thesis
      proof -
        have "\<forall>p. \<exists>c x. p = (c::('a, 'b, 'c,'d) LanguageCon.com, x::('a, 'c) xstate)"
          by auto
        thus ?thesis
          by (metis (no_types) Seqc Trans.hyps(3) Trans.prems(1) Trans.prems(2) 
                   `\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow> cfg''` c_step converse_rtranclp_into_rtranclp)
      qed
  qed
qed


lemma CatchSteps_ce: 
  assumes steps: "\<Gamma>\<turnstile>\<^sub>ccfg\<^sub>1\<rightarrow>\<^sub>c\<^sub>e\<^sup>* cfg\<^sub>2"
  shows "\<And> c\<^sub>1 s c\<^sub>1' s'. \<lbrakk>cfg\<^sub>1 = (c\<^sub>1,s); cfg\<^sub>2=(c\<^sub>1',s')\<rbrakk>
          \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (Catch c\<^sub>1' c\<^sub>2, s')"
using steps
proof (induct rule: converse_rtranclp_induct [case_names Refl Trans])
  case Refl
  thus ?case
    by simp
next
  case (Trans cfg\<^sub>1 cfg'')
then have "\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow> cfg'' \<or> \<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow>\<^sub>e cfg''" 
   using step_ce_elim_cases by blast
  thus ?case 
  proof
    assume a1:"\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow>\<^sub>e cfg''"        
    have "\<forall>f p pa. \<not> f\<turnstile>\<^sub>c p \<rightarrow>\<^sub>e pa \<or> (\<exists>c. (\<exists>x. p = (c::('a, 'b, 'c,'d) LanguageCon.com, x)) \<and> (\<exists>x. pa = (c, x)))"
      by (meson etranE)
    then obtain cc :: "('b \<Rightarrow>('a, 'b, 'c, 'd) LanguageCon.com option) \<Rightarrow>
                        ('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow>
                        ('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow>
                        ('a, 'b, 'c, 'd) LanguageCon.com" and 
                xx :: "('b \<Rightarrow>('a, 'b, 'c, 'd) LanguageCon.com option) \<Rightarrow>
                       ('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow>
                       ('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> 
                       ('a, 'c) xstate" and 
                xxa :: "('b \<Rightarrow>('a, 'b, 'c, 'd) LanguageCon.com option) \<Rightarrow>
                         ('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow>
                         ('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> ('a, 'c) xstate" where
      f1: "\<forall>f p pa. \<not> f\<turnstile>\<^sub>c p \<rightarrow>\<^sub>e pa \<or> p = (cc f p pa, xx f p pa) \<and> pa = (cc f p pa, xxa f p pa)"
      by (metis (no_types))
    have f2: "\<forall>f c x xa. \<not> f\<turnstile>\<^sub>c (c::('a, 'b, 'c,'d) LanguageCon.com, x) \<rightarrow>\<^sub>e (c, xa) \<or> 
                         (\<exists>a. x = Normal a) \<or> (\<forall>a. xa \<noteq> Normal a) \<and> x = xa"
      by (metis stepe_elim_cases)
    have f3: "(c\<^sub>1, xxa \<Gamma> cfg\<^sub>1 cfg'') = cfg''"
      using f1 by (metis Trans.prems(1) a1 fst_conv)
    hence "\<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Catch c\<^sub>1 c\<^sub>2, xxa \<Gamma> cfg\<^sub>1 cfg'') \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (LanguageCon.com.Catch c\<^sub>1' c\<^sub>2, s')"
      using Trans.hyps(3) Trans.prems(2) by force
    thus ?thesis
      using f3 f2 by (metis (no_types) Env Trans.prems(1) a1 e_step r_into_rtranclp rtranclp.rtrancl_into_rtrancl rtranclp_idemp)              
  next
    assume "\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow> cfg''"
    thus ?thesis
    proof -
      obtain cc :: "('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> ('a, 'b, 'c, 'd) LanguageCon.com" and xx :: "('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> ('a, 'c) xstate" where
        f1: "\<forall>p. p = (cc p, xx p)"
        by (meson old.prod.exhaust)
      hence "\<And>c. \<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Catch c\<^sub>1 c, s) \<rightarrow> (LanguageCon.com.Catch (cc cfg'') c, xx cfg'')"
        by (metis (no_types) Catchc Trans.prems(1) `\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow> cfg''`)
      thus ?thesis
        using f1 by (meson Trans.hyps(3) Trans.prems(2) c_step converse_rtranclp_into_rtranclp)
    qed      
  qed
qed

lemma step_change_p_or_eq_Ns: 
    assumes step: "\<Gamma>\<turnstile>\<^sub>c (P,Normal s) \<rightarrow> (Q,s')"
    shows  "\<not>(P=Q)"
using step
proof (induct P arbitrary: Q s s')
qed(fastforce elim: stepc_Normal_elim_cases)+

 
lemma step_change_p_or_eq_s: 
    assumes step: "\<Gamma>\<turnstile>\<^sub>c (P,s) \<rightarrow> (Q,s')"
    shows  "\<not>(P=Q)"
using step
proof (induct P arbitrary: Q s s')
qed (fastforce elim: stepc_elim_cases)+

subsection {* Relation between @{term "stepc_rtrancl"} and @{term "cptn"} *}

lemma stepc_rtrancl_cptn:
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c,s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (cf,sf)"           
  shows "\<exists>xs. (\<Gamma>,(c, s)#xs) \<in> cptn \<and>(cf,sf) = (last ((c,s)#xs))"
using step 
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans]) 
  case Refl thus ?case using cptn.CptnOne by auto
next
  case (Trans c s c' s')  
  have "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', s') \<or> \<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', s')"
    by (meson Trans.hyps(1) step_ce.simps)
  then show ?case
  proof
    assume prem:"\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', s')"       
    then have ceqc':"c=c'" using prem env_c_c'
      by auto           
    obtain xs where xs_s:"(\<Gamma>, (c', s') # xs) \<in> cptn \<and> (cf, sf) = last ((c', s') # xs)"
      using Trans(3) by auto 
    then have xs_f: "(\<Gamma>, (c, s)#(c', s') # xs) \<in> cptn" 
    using cptn.CptnEnv ceqc'  prem by fastforce
    also have "last ((c', s') # xs) = last ((c,s)#(c', s') # xs)" by auto
    then have "(cf, sf) = last ((c, s) # (c', s') # xs)"
      using   xs_s by auto
    thus ?thesis
      using  xs_f by blast
  next
    assume prem:"\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', s')" 
    obtain xs where xs_s:"(\<Gamma>, (c', s') # xs) \<in> cptn \<and> (cf, sf) = last ((c', s') # xs) "
      using Trans(3) by auto 
    have "(\<Gamma>, (c, s) # (c', s') # xs) \<in> cptn" using cptn.CptnComp 
      using xs_s prem by blast 
    also have "last ((c', s') # xs) = last ((c,s)#(c', s') # xs)" by auto
    ultimately show ?thesis using xs_s by fastforce
  qed 
qed


lemma cptn_stepc_rtrancl:
  assumes cptn_step: "(\<Gamma>,(c, s)#xs) \<in> cptn" and
          cf_last:"(cf,sf) = (last ((c,s)#xs))"
  shows "\<Gamma>\<turnstile>\<^sub>c (c,s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (cf,sf)"
using cptn_step cf_last
proof (induct xs arbitrary: c s) 
  case Nil
  thus ?case by simp 
next
  case (Cons a xs c s) 
  then obtain ca sa where eq_pair: "a=(ca,sa)" and "(cf, sf) = last ((ca,sa) # xs) " 
       using Cons by (fastforce)  
  have f1: "\<forall>f p pa. \<not> (f::'a \<Rightarrow> ('b, _, 'c,'d) LanguageCon.com option)\<turnstile>\<^sub>c p \<rightarrow> pa \<or> f\<turnstile>\<^sub>c p \<rightarrow>\<^sub>c\<^sub>e pa"
    by (simp add: c_step)
  have f2: "(\<Gamma>, (c, s) # (ca, sa) # xs) \<in> cptn"
    using `(\<Gamma>, (c, s) # a # xs) \<in> cptn` eq_pair by blast
  have f3: "\<forall>f p pa. \<not> (f::'a \<Rightarrow> ('b, _, 'c,'d) LanguageCon.com option)\<turnstile>\<^sub>c p \<rightarrow>\<^sub>e pa \<or> f\<turnstile>\<^sub>c p \<rightarrow>\<^sub>c\<^sub>e pa"
    using e_step by blast
  have "\<forall>c x. (\<Gamma>, (c, x) # xs) \<notin> cptn \<or> (cf, sf) \<noteq> last ((c, x) # xs) \<or> \<Gamma>\<turnstile>\<^sub>c (c, x) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (cf, sf)"
    using Cons.hyps by blast
  thus ?case
    using f3 f2 f1 by (metis (no_types) `(cf, sf) = last ((ca, sa) # xs)` converse_rtranclp_into_rtranclp cptn_elim_cases(2)) 
qed

lemma three_elems_list:
  assumes a1:"length l > 2"
  shows "\<exists>a0 a1 a2 l1. l=a0#a1#a2#l1"
using a1 by (metis Cons_nth_drop_Suc One_nat_def Suc_1 Suc_leI add_lessD1 drop_0 length_greater_0_conv list.size(3) not_numeral_le_zero one_add_one)  

lemma cptn_stepc_rtran:
  assumes cptn_step: "(\<Gamma>,x#xs) \<in> cptn" and          
          a1:"Suc i < length (x#xs)"
  shows "\<Gamma>\<turnstile>\<^sub>c ((x#xs)!i) \<rightarrow>\<^sub>c\<^sub>e ((x#xs)!(Suc i))"
using cptn_step a1
proof (induct i arbitrary: x xs)
  case 0
    then obtain x1 xs1 where xs:"xs=x1#xs1"
      by (metis length_Cons less_not_refl list.exhaust list.size(3))    
    then have "(x#x1#xs1)!Suc 0 = x1" by fastforce  
    have x_x1_cptn:"(\<Gamma>,x#x1#xs1)\<in>cptn" using 0 xs by auto    
    then have "(\<Gamma>,x1#xs1)\<in>cptn"
      using cptn_dest_pair by fastforce
    then have "\<Gamma>\<turnstile>\<^sub>cx \<rightarrow>\<^sub>e x1 \<or> \<Gamma>\<turnstile>\<^sub>cx \<rightarrow> x1" 
      using cptn_elim_cases_pair x_x1_cptn  by blast        
    then have "\<Gamma>\<turnstile>\<^sub>c x \<rightarrow>\<^sub>c\<^sub>e x1"
      by (metis c_step e_step)
    then show ?case 
      by (simp add: xs)
next
   case (Suc i)
    then have "Suc i < length xs" by auto
    moreover then obtain x1 xs1 where xs:"xs=x1#xs1"
      by (metis (full_types) list.exhaust list.size(3) not_less0)
    moreover then have "(\<Gamma>,x1#xs1) \<in> cptn" using Suc cptn_dest_pair by blast
    ultimately have "\<Gamma>\<turnstile>\<^sub>c ((x1 # xs1) ! i) \<rightarrow>\<^sub>c\<^sub>e ((x1 # xs1) ! Suc i)" 
      using Suc by auto
    thus ?case using Suc xs by auto
qed 
     
      
lemma cptn_stepconf_rtrancl:
  assumes cptn_step: "(\<Gamma>,cfg1#xs) \<in> cptn" and
          cf_last:"cfg2 = (last (cfg1#xs))"
  shows "\<Gamma>\<turnstile>\<^sub>c cfg1 \<rightarrow>\<^sub>c\<^sub>e\<^sup>* cfg2"
using cptn_step cf_last
by (metis cptn_stepc_rtrancl prod.collapse)

lemma cptn_all_steps_rtrancl:
  assumes cptn_step: "(\<Gamma>,cfg1#xs) \<in> cptn"          
  shows "\<forall>i<length (cfg1#xs). \<Gamma>\<turnstile>\<^sub>c cfg1 \<rightarrow>\<^sub>c\<^sub>e\<^sup>* ((cfg1#xs)!i)"
using cptn_step 
proof (induct xs arbitrary: cfg1)
  case Nil thus ?case by auto
next
  case (Cons x xs1) thus ?case
  proof -
     have hyp:"\<forall>i<length (x # xs1). \<Gamma>\<turnstile>\<^sub>c x \<rightarrow>\<^sub>c\<^sub>e\<^sup>* ((x # xs1) ! i)"
       using Cons.hyps Cons.prems cptn_dest_pair by blast      
     thus ?thesis
     proof
     {
        fix i
        assume a0:"i<length (cfg1 # x # xs1)"
        then have "Suc 0 < length (cfg1 # x # xs1)"
          by simp
        hence "\<Gamma>\<turnstile>\<^sub>c (cfg1 # x # xs1) ! 0 \<rightarrow>\<^sub>c\<^sub>e ((cfg1 # x # xs1) ! Suc 0)"
          using Cons.prems cptn_stepc_rtran by blast
        then have "\<Gamma>\<turnstile>\<^sub>c cfg1 \<rightarrow>\<^sub>c\<^sub>e x" using Cons by simp
        also have  "i < Suc (Suc (length xs1))"
          using a0 by force
        ultimately have "\<Gamma>\<turnstile>\<^sub>c cfg1 \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (cfg1 # x # xs1) ! i" using hyp Cons
         using converse_rtranclp_into_rtranclp hyp less_Suc_eq_0_disj 
         by auto 
     } thus ?thesis by auto qed
  qed
qed

lemma cptn_env_same_prog:
assumes a0: "(\<Gamma>, l) \<in> cptn" and
        a1:  "\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))" and
        a2: "Suc j < length l"
shows "fst (l!j) =  fst (l!0)"
using a0 a1 a2
proof (induct j arbitrary: l)
  case 0 thus ?case by auto
next
  case (Suc j) 
    then have "fst (l!j) =  fst (l!0)" by fastforce
    thus ?case using Suc 
      by (metis (no_types) env_c_c' lessI prod.collapse)
qed

lemma takecptn_is_cptn [rule_format, elim!]:
  "\<forall>j. (\<Gamma>,c) \<in> cptn \<longrightarrow> (\<Gamma>, take (Suc j) c) \<in> cptn"
apply(induct "c")
 apply(force elim: cptn.cases)
apply clarify
apply(case_tac j)
 apply simp
 apply(rule CptnOne)
apply simp
apply(force intro:cptn.intros elim:cptn.cases)
done



lemma dropcptn_is_cptn [rule_format,elim!]:
  "\<forall>j<length c. (\<Gamma>,c) \<in> cptn \<longrightarrow> (\<Gamma>, drop j c) \<in> cptn"
apply(induct "c")
 apply(force elim: cptn.cases)
apply clarify
apply(case_tac j,simp+)
apply(erule cptn.cases)
  apply simp
 apply force
apply force
done

lemma takepar_cptn_is_par_cptn [rule_format,elim]:
  "\<forall>j. (\<Gamma>,c) \<in> par_cptn \<longrightarrow> (\<Gamma>,take (Suc j) c) \<in> par_cptn"
apply(induct "c")
 apply(force elim: cptn.cases)
apply clarify
apply(case_tac j,simp)
 apply(rule ParCptnOne)
apply(force intro:par_cptn.intros elim:par_cptn.cases)
done

lemma droppar_cptn_is_par_cptn [rule_format]:
  "\<forall>j<length c. (\<Gamma>,c) \<in> par_cptn \<longrightarrow> (\<Gamma>,drop j c) \<in> par_cptn"
apply(induct "c")
 apply(force elim: par_cptn.cases)
apply clarify
apply(case_tac j,simp+)
apply(erule par_cptn.cases)
  apply simp
 apply force
apply force
done


subsection\<open>Modular Definition of Computation\<close>
definition lift :: "('s,'p,'f,'e) com \<Rightarrow> ('s,'p,'f,'e) config \<Rightarrow> ('s,'p,'f,'e) config" where
  "lift Q \<equiv> \<lambda>(P, s).  ((Seq P Q), s)" 

definition lift_catch :: "('s,'p,'f,'e) com \<Rightarrow> ('s,'p,'f,'e) config \<Rightarrow> ('s,'p,'f,'e) config" where
  "lift_catch Q \<equiv> \<lambda>(P, s).  (Catch P Q, s)"     


inductive_set cptn_mod :: "(('s,'p,'f,'e) confs) set"
where
  CptnModOne: "(\<Gamma>,[(P, s)]) \<in> cptn_mod"
| CptnModEnv: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow>\<^sub>e (P,t);(\<Gamma>,(P, t)#xs) \<in> cptn_mod \<rbrakk> \<Longrightarrow> 
               (\<Gamma>,(P, s)#(P, t)#xs) \<in> cptn_mod"
| CptnModSkip: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow> (Skip,t); redex P = P;
                (\<Gamma>,(Skip, t)#xs) \<in> cptn_mod \<rbrakk> \<Longrightarrow> 
                (\<Gamma>,(P,s)#(Skip, t)#xs) \<in>cptn_mod"

| CptnModThrow: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow> (Throw,t); redex P = P;
                (\<Gamma>,(Throw, t)#xs) \<in> cptn_mod \<rbrakk> \<Longrightarrow> 
                (\<Gamma>,(P,s)#(Throw, t)#xs) \<in>cptn_mod"

| CptnModCondT: "\<lbrakk>(\<Gamma>,(P0, Normal s)#ys) \<in> cptn_mod; s \<in> b \<rbrakk> \<Longrightarrow> 
                (\<Gamma>,((Cond b P0 P1), Normal s)#(P0, Normal s)#ys) \<in> cptn_mod"
| CptnModCondF: "\<lbrakk>(\<Gamma>,(P1, Normal s)#ys) \<in> cptn_mod; s \<notin> b \<rbrakk> \<Longrightarrow> 
                (\<Gamma>,((Cond b P0 P1), Normal s)#(P1, Normal s)#ys) \<in> cptn_mod"
| CptnModSeq1: 
  "\<lbrakk>(\<Gamma>,(P0, s)#xs) \<in> cptn_mod; zs=map (lift P1) xs \<rbrakk> \<Longrightarrow> 
   (\<Gamma>,((Seq P0 P1), s)#zs) \<in> cptn_mod"

| CptnModSeq2: 
  "\<lbrakk>(\<Gamma>, (P0, s)#xs) \<in> cptn_mod; fst(last ((P0, s)#xs)) = Skip;
    (\<Gamma>,(P1, snd(last ((P0, s)#xs)))#ys) \<in> cptn_mod;
    zs=(map (lift P1) xs)@((P1, snd(last ((P0, s)#xs)))#ys) \<rbrakk> \<Longrightarrow> 
   (\<Gamma>,((Seq P0 P1), s)#zs) \<in> cptn_mod"
(*| CptnModSeq3:
  "\<lbrakk> (\<Gamma>,(P1, s)#xs) \<in> cptn_mod\<rbrakk> \<Longrightarrow> (\<Gamma>,((Seq Skip P1), s)#(P1, s)#xs) \<in> cptn_mod"*)

| CptnModSeq3: 
  "\<lbrakk>(\<Gamma>, (P0, Normal s)#xs) \<in> cptn_mod; 
    fst(last ((P0, Normal s)#xs)) = Throw;
    snd(last ((P0, Normal s)#xs)) = Normal s'; 
    (\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod; 
    zs=(map (lift P1) xs)@((Throw,Normal s')#ys) \<rbrakk> \<Longrightarrow>
   (\<Gamma>,((Seq P0 P1), Normal s)#zs) \<in> cptn_mod"

| CptnModWhile1: 
  "\<lbrakk>(\<Gamma>, (P, Normal s)#xs) \<in> cptn_mod; s \<in> b; 
    zs=map (lift (While b P)) xs \<rbrakk> \<Longrightarrow> 
    (\<Gamma>, ((While b P), Normal s)#
      ((Seq P (While b P)),Normal s)#zs) \<in> cptn_mod"

| CptnModWhile2: 
  "\<lbrakk> (\<Gamma>, (P, Normal s)#xs) \<in> cptn_mod; 
     fst(last ((P, Normal s)#xs))=Skip; s \<in> b; 
     zs=(map (lift (While b P)) xs)@
      (While b P, snd(last ((P, Normal s)#xs)))#ys; 
      (\<Gamma>,(While b P, snd(last ((P, Normal s)#xs)))#ys) \<in> 
        cptn_mod\<rbrakk> \<Longrightarrow> 
   (\<Gamma>,(While b P, Normal s)#
     (Seq P (While b P), Normal s)#zs) \<in> cptn_mod"

| CptnModWhile3: 
  "\<lbrakk> (\<Gamma>, (P, Normal s)#xs) \<in> cptn_mod; 
     fst(last ((P, Normal s)#xs))=Throw; s \<in> b;
     snd(last ((P, Normal s)#xs)) = Normal s'; 
    (\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod;  
     zs=(map (lift (While b P)) xs)@((Throw,Normal s')#ys)\<rbrakk> \<Longrightarrow> 
   (\<Gamma>,(While b P, Normal s)#
     (Seq P (While b P), Normal s)#zs) \<in> cptn_mod"

| CptnModCall: "\<lbrakk>(\<Gamma>,(bdy, Normal s)#ys) \<in> cptn_mod;\<Gamma> p = Some bdy; bdy\<noteq>Call p \<rbrakk> \<Longrightarrow> 
                (\<Gamma>,((Call p), Normal s)#(bdy, Normal s)#ys) \<in> cptn_mod" 
| CptnModDynCom: "\<lbrakk>(\<Gamma>,(c s, Normal s)#ys) \<in> cptn_mod \<rbrakk> \<Longrightarrow> 
                  (\<Gamma>,(DynCom c, Normal s)#(c s, Normal s)#ys) \<in> cptn_mod"

| CptnModGuard: "\<lbrakk>(\<Gamma>,(c, Normal s)#ys) \<in> cptn_mod; s \<in> g \<rbrakk> \<Longrightarrow> 
                 (\<Gamma>,(Guard f g c, Normal s)#(c, Normal s)#ys) \<in> cptn_mod"

| CptnModCatch1: "\<lbrakk>(\<Gamma>,(P0, s)#xs) \<in> cptn_mod; zs=map (lift_catch P1) xs \<rbrakk>
                 \<Longrightarrow> (\<Gamma>,((Catch P0 P1), s)#zs) \<in> cptn_mod"
| CptnModCatch2: 
  "\<lbrakk>(\<Gamma>, (P0, s)#xs) \<in> cptn_mod; fst(last ((P0, s)#xs)) = Skip; 
    (\<Gamma>,(Skip,snd(last ((P0, s)#xs)))#ys) \<in> cptn_mod;  
    zs=(map (lift_catch P1) xs)@((Skip,snd(last ((P0, s)#xs)))#ys) \<rbrakk> \<Longrightarrow> 
   (\<Gamma>,((Catch P0 P1), s)#zs) \<in> cptn_mod"

| CptnModCatch3: 
  "\<lbrakk>(\<Gamma>, (P0, Normal s)#xs) \<in> cptn_mod; fst(last ((P0, Normal s)#xs)) = Throw; 
  snd(last ((P0, Normal s)#xs)) = Normal s';
  (\<Gamma>,(P1, snd(last ((P0, Normal s)#xs)))#ys) \<in> cptn_mod; 
  zs=(map (lift_catch P1) xs)@((P1, snd(last ((P0, Normal s)#xs)))#ys) \<rbrakk> \<Longrightarrow> 
   (\<Gamma>,((Catch P0 P1), Normal s)#zs) \<in> cptn_mod"


lemmas CptnMod_induct = cptn_mod.induct [of _ "[(c,s)]", split_format (complete), case_names
CptnModOne CptnModEnv CptnModSkip CptnModThrow CptnModCondT CptnModCondF 
CptnModSeq1 CptnModSeq2 CptnModSeq3 CptnModSeq4 CptnModWhile1 CptnModWhile2 CptnModWhile3 CptnModCall CptnModDynCom CptnModGuard 
CptnModCatch1 CptnModCatch2 CptnModCatch3, induct set]

inductive_cases CptnMod_elim_cases [cases set]:
"(\<Gamma>,(Skip, s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Guard f g c, s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Basic f e, s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Spec r e, s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Seq c1 c2, s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Cond b c1 c2, s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Await b c2 e, s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Call p, s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(DynCom c,s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Throw,s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Catch c1 c2,s)#u#xs) \<in> cptn_mod"


inductive_cases CptnMod_Normal_elim_cases [cases set]:
"(\<Gamma>,(Skip, Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Guard f g c, Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Basic f e, Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Spec r e, Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Seq c1 c2, Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Cond b c1 c2, Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Await b c2 e, Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Call p, Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(DynCom c,Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Throw,Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Catch c1 c2,Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(P,Normal s)#(P,s')#xs) \<in> cptn_mod"
"(\<Gamma>,(P,Abrupt s)#(P,Abrupt s')#xs) \<in> cptn_mod"
"(\<Gamma>,(P,Stuck)#(P,Stuck)#xs) \<in> cptn_mod"
"(\<Gamma>,(P,Fault f)#(P,Fault f)#xs) \<in> cptn_mod"

inductive_cases CptnMod_env_elim_cases [cases set]:
"(\<Gamma>,(P,Normal s)#(P,s')#xs) \<in> cptn_mod"
"(\<Gamma>,(P,Abrupt s)#(P,Abrupt s')#xs) \<in> cptn_mod"
"(\<Gamma>,(P,Stuck)#(P,Stuck)#xs) \<in> cptn_mod"
"(\<Gamma>,(P,Fault f)#(P,Fault f)#xs) \<in> cptn_mod"


subsection \<open>Equivalence of small semantics and computational\<close>

lemma last_length: "((a#xs)!(length xs))=last (a#xs)"
  by (induct xs) auto

definition catch_cond 
where
"catch_cond zs Q xs P s s'' s' \<Gamma> \<equiv> (zs=(map (lift_catch Q) xs) \<or>
             ((fst(((P, s)#xs)!length xs)=Throw \<and>
               snd(last ((P, s)#xs)) = Normal s' \<and> s=Normal s''\<and>
               (\<exists>ys. (\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod \<and> 
                zs=(map (lift_catch Q) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
                ((fst(((P, s)#xs)!length xs)=Skip \<and> 
                 (\<exists>ys. (\<Gamma>,(Skip,snd(last ((P, s)#xs)))#ys) \<in> cptn_mod \<and>                   
                 zs=(map (lift_catch Q) xs)@((Skip,snd(last ((P, s)#xs)))#ys)))))
"

lemma div_catch: assumes cptn_m:"(\<Gamma>,list) \<in> cptn_mod"
shows "(\<forall>s P Q zs. list=(Catch P Q, s)#zs \<longrightarrow>
       (\<exists>xs s' s''. 
          (\<Gamma>,(P, s)#xs) \<in> cptn_mod  \<and> 
             catch_cond zs Q xs P s s'' s' \<Gamma>))  
            "
unfolding catch_cond_def
using cptn_m
proof (induct rule: cptn_mod.induct)
case (CptnModOne \<Gamma> P s)
  thus ?case using cptn_mod.CptnModOne by blast 
next
  case (CptnModSkip  \<Gamma> P s t xs) 
  from CptnModSkip.hyps
  have step: "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow> (Skip, t)" by auto
  from CptnModSkip.hyps
  have noskip: "~(P=Skip)" using stepc_elim_cases(1) by blast  
  have no_catch: "\<forall>p1 p2. \<not>(P=Catch p1 p2)" using CptnModSkip.hyps(2) redex_not_Catch by auto
  from CptnModSkip.hyps
  have in_cptn_mod: "(\<Gamma>, (Skip, t) # xs) \<in> cptn_mod" by auto  
  then show ?case using no_catch by simp
next
  case (CptnModThrow  \<Gamma> P s t xs) 
  from CptnModThrow.hyps
  have step: "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow> (Throw, t)" by auto 
  from CptnModThrow.hyps
  have in_cptn_mod: "(\<Gamma>, (Throw, t) # xs) \<in> cptn_mod" by auto 
  have no_catch: "\<forall>p1 p2. \<not>(P=Catch p1 p2)" using CptnModThrow.hyps(2) redex_not_Catch by auto
  then show ?case by auto
next
  case (CptnModCondT \<Gamma> P0 s ys b P1)
  thus ?case using CptnModOne by blast
next
  case (CptnModCondF \<Gamma> P0 s ys b P1)
  thus ?case using CptnModOne by blast
next
  case (CptnModCatch1 sa P Q zs)
  thus ?case by blast
next
  case (CptnModCatch2 \<Gamma> P0 s xs ys zs P1) 
  from CptnModCatch2.hyps(3) 
  have last:"fst (((P0, s) # xs) ! length xs) = Skip" 
       by (simp add: last_length) 
  have P0cptn:"(\<Gamma>, (P0, s) # xs) \<in> cptn_mod" by fact          
  then have "zs = map (lift_catch P1) xs @((Skip,snd(last ((P0, s)#xs)))#ys)" by (simp add:CptnModCatch2.hyps)
  show ?case
  proof -{
    fix sa P Q zsa    
    assume eq:"(Catch P0 P1, s) # zs = (Catch P Q, sa) # zsa"
    then have "P0 =P \<and> P1 = Q \<and> s=sa \<and> zs=zsa" by auto
    then have "(P0, s) = (P, sa)" by auto 
    have "last ((P0, s) # xs) = ((P, sa) # xs) ! length xs"
      by (simp add: `P0 = P \<and> P1 = Q \<and> s = sa \<and> zs = zsa` last_length)
    then have "zs = (map (lift_catch Q) xs)@((Skip,snd(last ((P0, s)#xs)))#ys)"
      using `P0 = P \<and> P1 = Q \<and> s = sa \<and> zs = zsa` `zs = map (lift_catch P1) xs @ ((Skip,snd(last ((P0, s)#xs)))#ys)` 
      by force    
    then have "(\<exists>xs s' s''. ((\<Gamma>,(P, s)#xs) \<in> cptn_mod  \<and> 
             ((zs=(map (lift_catch Q) xs) \<or>
             ((fst(((P, s)#xs)!length xs)=Throw \<and>
               snd(last ((P, s)#xs)) = Normal s' \<and>  s=Normal s''\<and>
               (\<exists>ys. (\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod \<and> 
                zs=(map (lift_catch Q) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
                (\<exists>ys. ((fst(((P, s)#xs)!length xs)=Skip \<and> (\<Gamma>,(Skip,snd(last ((P, s)#xs)))#ys) \<in> cptn_mod \<and>                 
                 zs=(map (lift_catch Q) xs)@((Skip,snd(last ((P0, s)#xs)))#ys))))))))"
    using P0cptn  `P0 = P \<and> P1 = Q \<and> s = sa \<and> zs = zsa`  last  CptnModCatch2.hyps(4) by blast 
   } 
   thus ?thesis by auto
  qed
next
  case (CptnModCatch3 \<Gamma> P0 s xs s' P1 ys zs)
  from CptnModCatch3.hyps(3)  
  have last:"fst (((P0, Normal s) # xs) ! length xs) = Throw" 
       by (simp add: last_length) 
  from CptnModCatch3.hyps(4) 
  have lastnormal:"snd (last ((P0, Normal s) # xs)) = Normal s'"
      by (simp add: last_length)
  have P0cptn:"(\<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod" by fact
  from CptnModCatch3.hyps(5) have P1cptn:"(\<Gamma>, (P1, snd (((P0, Normal s) # xs) ! length xs)) # ys) \<in> cptn_mod"
      by (simp add: last_length)          
  then have "zs = map (lift_catch P1) xs @ (P1, snd (last ((P0, Normal s) # xs))) # ys" by (simp add:CptnModCatch3.hyps)
  show ?case
  proof -{
    fix sa P Q zsa    
    assume eq:"(Catch P0 P1, Normal s) # zs = (Catch P Q, Normal sa) # zsa"
    then have "P0 =P \<and> P1 = Q \<and> Normal s= Normal sa \<and> zs=zsa" by auto     
    have "last ((P0, Normal s) # xs) = ((P, Normal sa) # xs) ! length xs"
      by (simp add: `P0 = P \<and> P1 = Q \<and> Normal s = Normal sa \<and> zs = zsa` last_length)
    then have "zsa = map (lift_catch Q) xs @ (Q, snd (((P, Normal sa) # xs) ! length xs)) # ys"
      using `P0 = P \<and> P1 = Q \<and> Normal s = Normal sa \<and> zs = zsa` `zs = map (lift_catch P1) xs @ (P1, snd (last ((P0, Normal s) # xs))) # ys` by force
    then have "(\<Gamma>, (P, Normal s) # xs) \<in> cptn_mod \<and> (fst(((P, Normal s)#xs)!length xs)=Throw \<and>
               snd(last ((P, Normal s)#xs)) = Normal s' \<and> 
              (\<exists>ys. (\<Gamma>,(Q, snd(((P, Normal s)#xs)!length xs))#ys) \<in> cptn_mod \<and> 
              zs=(map (lift_catch Q) xs)@((Q, snd(((P, Normal s)#xs)!length xs))#ys)))" 
      using lastnormal P1cptn P0cptn `P0 = P \<and> P1 = Q \<and> Normal s = Normal sa \<and> zs = zsa` last 
       by auto    
    }note this [of P0 P1 s zs] thus ?thesis by blast qed
next
  case (CptnModEnv \<Gamma> P s t xs)  
  then have step:"(\<Gamma>, (P, t) # xs) \<in> cptn_mod" by auto  
  have step_e: "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow>\<^sub>e (P, t)" using CptnModEnv by auto
  show ?case     
    proof (cases P)
      case (Catch P1 P2) 
      then have eq_P_Catch:"(P, t) # xs = (LanguageCon.com.Catch P1 P2, t) # xs" by auto      
      then  obtain xsa t' t'' where 
         p1:"(\<Gamma>, (P1, t) # xsa) \<in> cptn_mod" and p2:"
     (xs = map (lift_catch P2) xsa \<or>
      fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Throw \<and>
      snd (last ((P1, t) # xsa)) = Normal t' \<and>
      t = Normal t'' \<and>
      (\<exists>ys. (\<Gamma>, (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<in> cptn_mod \<and>
            xs =
            map (lift_catch P2) xsa @
            (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<or>
            fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Skip \<and>
            (\<exists>ys.(\<Gamma>,(Skip,snd(last ((P1, t)#xsa)))#ys) \<in> cptn_mod \<and> 
            xs = map (lift_catch P2) xsa @
            ((LanguageCon.com.Skip, snd (last ((P1, t) # xsa)))#ys)))" 
        using CptnModEnv(3) by auto
      have all_step:"(\<Gamma>, (P1, s)#((P1, t) # xsa)) \<in> cptn_mod"
        by (metis p1 Env Env_n cptn_mod.CptnModEnv env_normal_s step_e)       
      show ?thesis using p2 
      proof  
        assume "xs = map (lift_catch P2) xsa"
        have "(P, t) # xs = map (lift_catch P2) ((P1, t) # xsa)"
          by (simp add: `xs = map (lift_catch P2) xsa` lift_catch_def local.Catch)
        thus ?thesis using all_step eq_P_Catch by fastforce
      next 
        assume 
         "fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Throw \<and>
          snd (last ((P1, t) # xsa)) = Normal t' \<and>
          t = Normal t'' \<and>
          (\<exists>ys. (\<Gamma>, (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<in> cptn_mod \<and>
                xs =
                map (lift_catch P2) xsa @
                (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<or>
                fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Skip \<and>
           (\<exists>ys. (\<Gamma>,(Skip,snd(last ((P1, t)#xsa)))#ys) \<in> cptn_mod \<and> 
            xs = map (lift_catch P2) xsa @
            ((LanguageCon.com.Skip, snd (last ((P1, t) # xsa)))#ys))"      
         then show ?thesis 
         proof
           assume 
            a1:"fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Throw \<and>
             snd (last ((P1, t) # xsa)) = Normal t' \<and>
             t = Normal t'' \<and>
             (\<exists>ys. (\<Gamma>, (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<in> cptn_mod \<and>
                xs = map (lift_catch P2) xsa @
                       (P2, snd (((P1, t) # xsa) ! length xsa)) # ys)"
            then obtain ys where p2_exec:"(\<Gamma>, (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<in> cptn_mod \<and>
                xs = map (lift_catch P2) xsa @
                       (P2, snd (((P1, t) # xsa) ! length xsa)) # ys" 
            by fastforce
            from a1 obtain t1 where t_normal: "t=Normal t1" 
              using env_normal_s'_normal_s by blast
            have f1:"fst (((P1, s)#(P1, t) # xsa) ! length ((P1, t)#xsa)) = LanguageCon.com.Throw"
              using a1 by fastforce
             from a1 have last_normal: "snd (last ((P1, s)#(P1, t) # xsa)) = Normal t'"
               by fastforce 
             then have p2_long_exec: "(\<Gamma>, (P2, snd (((P1, s)#(P1, t) # xsa) ! length ((P1, s)#xsa))) # ys) \<in> cptn_mod \<and>
                (P, t)#xs = map (lift_catch P2) ((P1, t) # xsa) @
                       (P2, snd (((P1, s)#(P1, t) # xsa) ! length ((P1, s)#xsa))) # ys" using p2_exec 
                by (simp add: lift_catch_def local.Catch)                  
             thus ?thesis using  a1 f1 last_normal all_step eq_P_Catch 
               by (clarify, metis (no_types) list.size(4) not_step_c_env  step_e)            
           next
           assume 
            as1:"fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Skip \<and>
           (\<exists>ys. (\<Gamma>,(Skip,snd(last ((P1, t)#xsa)))#ys) \<in> cptn_mod \<and> 
            xs = map (lift_catch P2) xsa @
            ((LanguageCon.com.Skip, snd (last ((P1, t) # xsa)))#ys))"               
            then obtain ys where p1:"(\<Gamma>,(Skip,snd(last ((P1, t)#xsa)))#ys) \<in> cptn_mod \<and> 
                         (P, t)#xs = map (lift_catch P2) ((P1, t) # xsa) @
                          ((LanguageCon.com.Skip, snd (last ((P1, t) # xsa)))#ys)"
            proof -
              assume a1: "\<And>ys. (\<Gamma>, (LanguageCon.com.Skip, snd (last ((P1, t) # xsa))) # ys) \<in> cptn_mod \<and> (P, t) # xs = map (lift_catch P2) ((P1, t) # xsa) @ (LanguageCon.com.Skip, snd (last ((P1, t) # xsa))) # ys \<Longrightarrow> thesis"
              have "(LanguageCon.com.Catch P1 P2, t) # map (lift_catch P2) xsa = map (lift_catch P2) ((P1, t) # xsa)"
                by (simp add: lift_catch_def)
              thus ?thesis
                using a1 as1 eq_P_Catch by moura
            qed            
            from as1 have p2: "fst (((P1, s)#(P1, t) # xsa) ! length ((P1, t) #xsa)) = LanguageCon.com.Skip"
                 by fastforce                              
            thus ?thesis using p1 all_step eq_P_Catch by fastforce
          qed
      qed
    qed (auto)
qed(force+)


definition seq_cond 
where
"seq_cond zs Q xs P s s'' s' \<Gamma> \<equiv> (zs=(map (lift Q) xs) \<or>
             ((fst(((P, s)#xs)!length xs)=Skip \<and> 
               (\<exists>ys. (\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod \<and> 
                zs=(map (lift (Q)) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
             ((fst(((P, s)#xs)!length xs)=Throw \<and> 
                 snd(last ((P, s)#xs)) = Normal s' \<and>  s=Normal s''\<and>
                 (\<exists>ys.  (\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod \<and>
                      zs=(map (lift Q) xs)@((Throw,Normal s')#ys)))))
"

lemma div_seq: assumes cptn_m:"(\<Gamma>,list) \<in> cptn_mod"
shows "(\<forall>s P Q zs. list=(Seq P Q, s)#zs \<longrightarrow>
       (\<exists>xs s' s''. 
          (\<Gamma>,(P, s)#xs) \<in> cptn_mod  \<and> 
             seq_cond zs Q xs P s s'' s' \<Gamma>))  
            "
unfolding seq_cond_def
using cptn_m
proof (induct rule: cptn_mod.induct)
  case (CptnModOne \<Gamma> P s)
  thus ?case using cptn_mod.CptnModOne by blast 
next
  case (CptnModSkip  \<Gamma> P s t xs) 
  from CptnModSkip.hyps
  have step: "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow> (Skip, t)" by auto
  from CptnModSkip.hyps
  have noskip: "~(P=Skip)" using stepc_elim_cases(1) by blast  
  have x: "\<forall>c c1 c2. redex c = Seq c1 c2 \<Longrightarrow> False"
          using redex_not_Seq by blast
  from CptnModSkip.hyps
  have in_cptn_mod: "(\<Gamma>, (Skip, t) # xs) \<in> cptn_mod" by auto  
  then show ?case using CptnModSkip.hyps(2) SmallStepCon.redex_not_Seq by blast
next
  case (CptnModThrow  \<Gamma> P s t xs)
  from CptnModThrow.hyps
  have step: "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow> (Throw, t)" by auto 
  moreover from CptnModThrow.hyps
  have in_cptn_mod: "(\<Gamma>, (Throw, t) # xs) \<in> cptn_mod" by auto 
  have no_seq: "\<forall>p1 p2. \<not>(P=Seq p1 p2)" using CptnModThrow.hyps(2) redex_not_Seq by auto
  ultimately show ?case by auto   
next 
  case (CptnModCondT \<Gamma> P0 s ys b P1)
  thus ?case by auto
next
  case (CptnModCondF \<Gamma> P0 s ys b P1)
  thus ?case by auto
next
  case (CptnModSeq1 \<Gamma> P0 s xs zs P1)
  thus ?case by blast
next 
  case (CptnModSeq2 \<Gamma> P0 s xs P1 ys zs) 
  from CptnModSeq2.hyps(3) last_length have last:"fst (((P0, s) # xs) ! length xs) = Skip" 
       by (simp add: last_length) 
  have P0cptn:"(\<Gamma>, (P0, s) # xs) \<in> cptn_mod" by fact
  from CptnModSeq2.hyps(4) have P1cptn:"(\<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod"
      by (simp add: last_length)          
  then have "zs = map (lift P1) xs @ (P1, snd (last ((P0, s) # xs))) # ys" by (simp add:CptnModSeq2.hyps)
  show ?case
  proof -{
    fix sa P Q zsa    
    assume eq:"(Seq P0 P1, s) # zs = (Seq P Q, sa) # zsa"
    then have "P0 =P \<and> P1 = Q \<and> s=sa \<and> zs=zsa" by auto 
     have "last ((P0, s) # xs) = ((P, sa) # xs) ! length xs"
            by (simp add: `P0 = P \<and> P1 = Q \<and> s = sa \<and> zs = zsa` last_length)
    then have "zsa = map (lift Q) xs @ (Q, snd (((P, sa) # xs) ! length xs)) # ys"
         using `P0 = P \<and> P1 = Q \<and> s = sa \<and> zs = zsa` `zs = map (lift P1) xs @ (P1, snd (last ((P0, s) # xs))) # ys` 
         by force    
    then have "(\<exists>xs s' s''. (\<Gamma>, (P, sa) # xs) \<in> cptn_mod \<and>
                        (zsa = map (lift Q) xs \<or>              
                         fst (((P, sa) # xs) ! length xs) = Skip \<and>
                             (\<exists>ys. (\<Gamma>, (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<in> cptn_mod \<and>
                             zsa = map (lift Q) xs @ (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<or>
                        ((fst(((P, sa)#xs)!length xs)=Throw \<and> 
                          snd(last ((P, sa)#xs)) = Normal s' \<and>  s=Normal s''\<and>
                         (\<exists>ys. (\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod \<and>
                               zsa=(map (lift Q) xs)@((Throw,Normal s')#ys))))))
               " 
        using P0cptn P1cptn  `P0 = P \<and> P1 = Q \<and> s = sa \<and> zs = zsa` last 
        by blast                 
   }  
   thus ?case by auto qed     
next
  case (CptnModSeq3 \<Gamma> P0 s xs s' ys zs P1) 
  from CptnModSeq3.hyps(3) 
  have last:"fst (((P0, Normal s) # xs) ! length xs) = Throw" 
       by (simp add: last_length) 
  have P0cptn:"(\<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod" by fact
  from CptnModSeq3.hyps(4) 
  have lastnormal:"snd (last ((P0, Normal s) # xs)) = Normal s'"
      by (simp add: last_length)          
  then have "zs = map (lift P1) xs @ ((Throw, Normal s')#ys)" by (simp add:CptnModSeq3.hyps)
  show ?case
  proof -{
    fix sa P Q zsa    
    assume eq:"(Seq P0 P1, Normal s) # zs = (Seq P Q, Normal sa) # zsa"
    then have "P0 =P \<and> P1 = Q \<and> Normal s=Normal sa \<and> zs=zsa" by auto
    then have "(P0, Normal s) = (P, Normal sa)" by auto 
    have "last ((P0, Normal s) # xs) = ((P, Normal sa) # xs) ! length xs"
                    by (simp add: `P0 = P \<and> P1 = Q \<and> Normal s = Normal sa \<and> zs = zsa` last_length)
    then have zsa:"zsa = (map (lift Q) xs)@((Throw,Normal s')#ys)"
                    using `P0 = P \<and> P1 = Q \<and> Normal s = Normal sa \<and> zs = zsa` `zs = map (lift P1) xs @ ((Throw, Normal s')#ys)` 
    by force
    then have a1:"(\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod" using CptnModSeq3.hyps(5) by blast               
     have "(P, Normal sa::('b, 'c) xstate) = (P0, Normal s)"
    using `P0 = P \<and> P1 = Q \<and> Normal s = Normal sa \<and> zs = zsa` by auto  
    then have "(\<exists>xs s'. (\<Gamma>, (P, Normal sa) # xs) \<in> cptn_mod \<and>
                        (zsa = map (lift Q) xs \<or>              
                         fst (((P,Normal sa) # xs) ! length xs) = Skip \<and>
                             (\<exists>ys. (\<Gamma>, (Q, snd (((P, Normal sa) # xs) ! length xs)) # ys) \<in> cptn_mod \<and>
                             zsa = map (lift Q) xs @ (Q, snd (((P, Normal sa) # xs) ! length xs)) # ys) \<or>
                        ((fst(((P, Normal sa)#xs)!length xs)=Throw \<and> 
                          snd(last ((P, Normal sa)#xs)) = Normal s' \<and>
                          (\<exists>ys. (\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod \<and>
                          zsa=(map (lift Q) xs)@((Throw,Normal s')#ys))))))"
     using P0cptn zsa a1 last lastnormal 
       by blast 
   }  
   thus ?thesis by auto qed  
next 
  case (CptnModEnv \<Gamma> P s t zs) 
  then have step:"(\<Gamma>, (P, t) # zs) \<in> cptn_mod" by auto
  have step_e: "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow>\<^sub>e (P, t)" using CptnModEnv by auto  
  show ?case     
    proof (cases P)
      case (Seq P1 P2) 
      then have eq_P:"(P, t) # zs = (LanguageCon.com.Seq P1 P2, t) # zs" by auto      
      then  obtain xs t' t'' where 
         p1:"(\<Gamma>, (P1, t) # xs) \<in> cptn_mod" and p2:"
     (zs = map (lift P2) xs \<or>
      fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Skip \<and>      
      (\<exists>ys. (\<Gamma>, (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<in> cptn_mod \<and>
            zs =
            map (lift P2) xs @
            (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<or>
      fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Throw \<and>
      snd (last ((P1, t) # xs)) = Normal t' \<and>
      t = Normal t'' \<and> (\<exists>ys. (\<Gamma>,(Throw,Normal t')#ys) \<in> cptn_mod \<and> 
      zs =
      map (lift P2) xs @
      ((LanguageCon.com.Throw, Normal t')#ys))) " 
        using CptnModEnv(3) by auto
      have all_step:"(\<Gamma>, (P1, s)#((P1, t) # xs)) \<in> cptn_mod"
       by (metis p1 Env Env_n cptn_mod.CptnModEnv env_normal_s step_e)         
      show ?thesis using p2 
      proof  
        assume "zs = map (lift P2) xs"
        have "(P, t) # zs = map (lift P2) ((P1, t) # xs)"
          by (simp add: `zs = map (lift P2) xs` lift_def local.Seq)
        thus ?thesis using all_step eq_P by fastforce
      next 
        assume 
         "fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Skip \<and>      
         (\<exists>ys. (\<Gamma>, (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<in> cptn_mod \<and>
            zs = map (lift P2) xs @ (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<or>
          fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Throw \<and>
           snd (last ((P1, t) # xs)) = Normal t' \<and>
           t = Normal t'' \<and> (\<exists>ys. (\<Gamma>,(Throw,Normal t')#ys) \<in> cptn_mod \<and> 
           zs = map (lift P2) xs @ ((LanguageCon.com.Throw, Normal t')#ys))"
         then show ?thesis 
         proof
           assume 
            a1:"fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Skip \<and>      
               (\<exists>ys. (\<Gamma>, (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<in> cptn_mod \<and>
               zs = map (lift P2) xs @ (P2, snd (((P1, t) # xs) ! length xs)) # ys)"
               from a1 obtain ys where 
                   p2_exec:"(\<Gamma>, (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<in> cptn_mod \<and>
                       zs = map (lift P2) xs @
                       (P2, snd (((P1, t) # xs) ! length xs)) # ys" 
                by auto 
               have f1:"fst (((P1, s)#(P1, t) # xs) ! length ((P1, t)#xs)) = LanguageCon.com.Skip"
                 using a1 by fastforce             
               then have p2_long_exec: 
                 "(\<Gamma>, (P2, snd (((P1, s)#(P1, t) # xs) ! length ((P1, t)#xs))) # ys) \<in> cptn_mod \<and>
                  (P, t)#zs = map (lift P2) ((P1, t) # xs) @
                       (P2, snd (((P1, s)#(P1, t) # xs) ! length ((P1, t)#xs))) # ys" 
             using p2_exec by (simp add: lift_def local.Seq)     
             thus ?thesis using a1 f1 all_step eq_P by blast            
           next
           assume 
            a1:"fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Throw \<and>
            snd (last ((P1, t) # xs)) = Normal t' \<and> t = Normal t'' \<and> 
          (\<exists>ys. (\<Gamma>,(Throw,Normal t')#ys) \<in> cptn_mod \<and> 
           zs = map (lift P2) xs @ ((LanguageCon.com.Throw, Normal t')#ys))"             
             then have last_throw:
               "fst (((P1, s)#(P1, t) # xs) ! length ((P1, t) #xs)) = LanguageCon.com.Throw" 
               by fastforce
             from a1 have last_normal: "snd (last ((P1, s)#(P1, t) # xs)) = Normal t'"
               by fastforce
             have seq_lift:
               "(LanguageCon.com.Seq P1 P2, t) # map (lift P2) xs = map (lift P2) ((P1, t) # xs)"
                by (simp add: a1 lift_def)             
            thus  ?thesis using a1 last_throw last_normal all_step eq_P         
              by (clarify, metis (no_types, lifting) append_Cons env_normal_s'_normal_s  step_e)                 
          qed
      qed
    qed (auto) 
qed (force)+


lemma cptn_onlyif_cptn_mod_aux:
assumes stepseq:"\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow> (Q,t)" and
        stepmod:"(\<Gamma>,(Q,t)#xs) \<in> cptn_mod"
shows "(\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptn_mod"
using stepseq stepmod
proof (induct arbitrary: xs)
  case (Basicc f s) 
  thus ?case by (simp add: cptn_mod.CptnModSkip stepc.Basicc)
next
  case (Specc s t r)
  thus ?case by (simp add: cptn_mod.CptnModSkip stepc.Specc) 
next
  case (SpecStuckc s r)
  thus ?case by (simp add: cptn_mod.CptnModSkip stepc.SpecStuckc)
next
  case (Guardc s g f c)
  thus ?case by (simp add: cptn_mod.CptnModGuard) 
next
  case (GuardFaultc)
  thus ?case by (simp add: cptn_mod.CptnModSkip stepc.GuardFaultc)
next
  case (Seqc c1 s c1' s' c2)
  have step: "\<Gamma>\<turnstile>\<^sub>c (c1, s) \<rightarrow> (c1', s')" by (simp add: Seqc.hyps(1))
  then have nsc1: "c1\<noteq>Skip" using stepc_elim_cases(1) by blast 
  have assum: "(\<Gamma>, (Seq c1' c2, s') # xs) \<in> cptn_mod" using Seqc.prems by blast
  have divseq:"(\<forall>s P Q zs. (Seq c1' c2, s') # xs=(Seq P Q, s)#zs \<longrightarrow>
                (\<exists>xs sv' sv''. ((\<Gamma>,(P, s)#xs) \<in> cptn_mod  \<and> 
                           (zs=(map (lift Q) xs) \<or>
                           ((fst(((P, s)#xs)!length xs)=Skip \<and> 
                             (\<exists>ys. (\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod \<and> 
                              zs=(map (lift (Q)) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
                           ((fst(((P, s)#xs)!length xs)=Throw \<and> 
                               snd(last ((P, s)#xs)) = Normal sv' \<and>  s'=Normal sv''\<and>
                             (\<exists>ys.  (\<Gamma>,(Throw,Normal sv')#ys) \<in> cptn_mod \<and>
                              zs=(map (lift Q) xs)@((Throw,Normal sv')#ys))
                               ))))
                            
                 ))"  using div_seq [OF assum] unfolding seq_cond_def by auto
   {fix sa P Q zsa
       assume ass:"(Seq c1' c2, s') # xs = (Seq P Q, sa) # zsa"
       then have eqs:"c1' = P \<and> c2 = Q \<and> s' = sa \<and> xs = zsa" by auto
       then have "(\<exists>xs sv' sv''. (\<Gamma>, (P, sa) # xs) \<in> cptn_mod \<and>
                        (zsa = map (lift Q) xs \<or>              
                         fst (((P, sa) # xs) ! length xs) = Skip \<and>
                             (\<exists>ys. (\<Gamma>, (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<in> cptn_mod \<and>
                             zsa = map (lift Q) xs @ (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<or>
                        ((fst(((P, sa)#xs)!length xs)=Throw \<and> 
                          snd(last ((P, sa)#xs)) = Normal sv' \<and>  s'=Normal sv''\<and>
                          (\<exists>ys.  (\<Gamma>,(Throw,Normal sv')#ys) \<in> cptn_mod \<and>
                              zsa=(map (lift Q) xs)@((Throw,Normal sv')#ys))))))" 
             using ass divseq by blast
    } note conc=this [of c1' c2 s' xs]    
     then obtain xs' sa' sa''
       where  split:"(\<Gamma>, (c1', s') # xs') \<in> cptn_mod \<and>
                     (xs = map (lift c2) xs' \<or>                   
                     fst (((c1', s') # xs') ! length xs') = Skip \<and>
                        (\<exists>ys. (\<Gamma>, (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<in> cptn_mod \<and>
                         xs = map (lift c2) xs' @ (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<or>
                     ((fst(((c1', s')#xs')!length xs')=Throw \<and> 
                         snd(last ((c1', s')#xs')) = Normal sa' \<and> s'=Normal sa''\<and>
                         (\<exists>ys.  (\<Gamma>,(Throw,Normal sa')#ys) \<in> cptn_mod \<and>
                              xs=(map (lift c2) xs')@((Throw,Normal sa')#ys))
                         )))"  by blast
  then have "(xs = map (lift c2) xs' \<or>                   
                     fst (((c1', s') # xs') ! length xs') = Skip \<and>
                        (\<exists>ys. (\<Gamma>, (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<in> cptn_mod \<and>
                         xs = map (lift c2) xs' @ (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<or>
                     ((fst(((c1', s')#xs')!length xs')=Throw \<and> 
                         snd(last ((c1', s')#xs')) = Normal sa' \<and> s'=Normal sa''\<and>
                         (\<exists>ys.  (\<Gamma>,(Throw,Normal sa')#ys) \<in> cptn_mod \<and>
                              xs=(map (lift c2) xs')@((Throw,Normal sa')#ys)))))" by auto
  thus ?case 
  proof{           
       assume c1'nonf:"xs = map (lift c2) xs'"
       then have c1'cptn:"(\<Gamma>, (c1', s') # xs') \<in> cptn_mod" using split by blast
       then have induct_step: "(\<Gamma>, (c1, s) # (c1', s')#xs') \<in> cptn_mod"
         using Seqc.hyps(2)  by blast
       then have "(Seq c1' c2, s')#xs = map (lift c2) ((c1', s')#xs')"
            using c1'nonf
            by (simp add: CptnModSeq1 lift_def)
       thus ?thesis 
            using c1'nonf c1'cptn induct_step by (auto simp add: CptnModSeq1)
    next
      assume "fst (((c1', s') # xs') ! length xs') = Skip \<and>
              (\<exists>ys. (\<Gamma>, (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<in> cptn_mod \<and>
                  xs = map (lift c2) xs' @ (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<or>
             ((fst(((c1', s')#xs')!length xs')=Throw \<and> 
                snd(last ((c1', s')#xs')) = Normal sa' \<and>  s'=Normal sa''\<and>
                (\<exists>ys.  (\<Gamma>,(Throw,Normal sa')#ys) \<in> cptn_mod \<and>
                              xs=(map (lift c2) xs')@((Throw,Normal sa')#ys))))"  
      thus ?thesis
      proof
         assume assth:"fst (((c1', s') # xs') ! length xs') = Skip \<and>
              (\<exists>ys. (\<Gamma>, (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<in> cptn_mod \<and>
                  xs = map (lift c2) xs' @ (c2, snd (((c1', s') # xs') ! length xs')) # ys)"
         then obtain ys 
             where split':"(\<Gamma>, (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<in> cptn_mod \<and>
                  xs = map (lift c2) xs' @ (c2, snd (((c1', s') # xs') ! length xs')) # ys"
             by auto    
         then have c1'cptn:"(\<Gamma>, (c1', s') # xs') \<in> cptn_mod" using split by blast
         then have induct_step: "(\<Gamma>, (c1, s) # (c1', s')#xs') \<in> cptn_mod"
         using Seqc.hyps(2)  by blast                
         then have seqmap:"(Seq c1 c2, s)#(Seq c1' c2, s')#xs = map (lift c2) ((c1,s)#(c1', s')#xs') @ (c2, snd (((c1', s') # xs') ! length xs')) # ys"
        using split'   
         by (simp add: CptnModSeq2 lift_def) 
        then have lastc1:"last ((c1, s) # (c1', s') # xs') = ((c1', s') # xs') ! length xs'"
          by (simp add: last_length) 
        then have lastc1skip:"fst (last ((c1, s) # (c1', s') # xs')) = Skip" 
          using assth by fastforce          
        thus ?thesis 
           using seqmap split' last_length cptn_mod.CptnModSeq2 
                 induct_step lastc1 lastc1skip 
           by fastforce
    next
        assume assm:"((fst(((c1', s')#xs')!length xs')=Throw \<and> 
                snd(last ((c1', s')#xs')) = Normal sa' \<and>  s'=Normal sa''\<and>
                (\<exists>ys.  (\<Gamma>,(Throw,Normal sa')#ys) \<in> cptn_mod \<and>
                 xs=(map (lift c2) xs')@((Throw,Normal sa')#ys))))"
        then have s'eqsa'': "s'=Normal sa''" by auto
        then have snormal: "\<exists>ns. s=Normal ns" by (metis Seqc.hyps(1) step_Abrupt_prop step_Fault_prop step_Stuck_prop xstate.exhaust)
        then have c1'cptn:"(\<Gamma>, (c1', s') # xs') \<in> cptn_mod" using split by blast        
        then have induct_step: "(\<Gamma>, (c1, s) # (c1', s')#xs') \<in> cptn_mod"
        using Seqc.hyps(2)  by blast 
        then obtain ys where seqmap:"(Seq c1' c2, s')#xs = (map (lift c2) ((c1', s')#xs'))@((Throw,Normal sa')#ys)"
        using assm
        proof -
          assume a1: "\<And>ys. (LanguageCon.com.Seq c1' c2, s') # xs = map (lift c2) ((c1', s') # xs') @ (LanguageCon.com.Throw, Normal sa') # ys \<Longrightarrow> thesis"
          have "(LanguageCon.com.Seq c1' c2, Normal sa'') # map (lift c2) xs' = map (lift c2) ((c1', s') # xs')"
            by (simp add: assm lift_def)
          thus ?thesis
            using a1 assm by moura
        qed  
        then have lastc1:"last ((c1, s) # (c1', s') # xs') = ((c1', s') # xs') ! length xs'"
                   by (simp add: last_length) 
        then have lastc1skip:"fst (last ((c1, s) # (c1', s') # xs')) = Throw" 
             using assm by fastforce
        then have "snd (last ((c1, s) # (c1', s') # xs')) = Normal sa'"
             using assm by force        
        thus ?thesis
            using assm c1'cptn induct_step lastc1skip snormal seqmap s'eqsa'' 
            by (auto simp add:cptn_mod.CptnModSeq3)
   qed
  }qed    
          
next
  case (SeqSkipc c2 s xs)
  have c2incptn:"(\<Gamma>, (c2, s) # xs) \<in> cptn_mod" by fact
  then have 1:"(\<Gamma>, [(Skip, s)]) \<in> cptn_mod" by (simp add: cptn_mod.CptnModOne)
  then have 2:"fst(last ([(Skip, s)])) = Skip" by fastforce
  then have 3:"(\<Gamma>,(c2, snd(last [(Skip, s)]))#xs) \<in> cptn_mod" 
      using c2incptn by auto  
  then have "(c2,s)#xs=(map (lift c2) [])@(c2, snd(last [(Skip, s)]))#xs" 
       by (auto simp add:lift_def)
  thus ?case using 1 2 3 by (simp add: CptnModSeq2)
next
  case (SeqThrowc c2 s xs)  
  have "(\<Gamma>, [(Throw, Normal s)]) \<in> cptn_mod" by (simp add: cptn_mod.CptnModOne) 
  then obtain ys where ys_nil:"ys=[]" and last:"(\<Gamma>, (Throw, Normal s)#ys)\<in> cptn_mod"
   by auto
  moreover have "fst (last ((Throw, Normal s)#ys)) = Throw" using ys_nil last by auto
  moreover have "snd (last ((Throw, Normal s)#ys)) = Normal s" using ys_nil last by auto
  moreover from ys_nil have "(map (lift c2) ys) = []" by auto  
  ultimately show ?case using SeqThrowc.prems cptn_mod.CptnModSeq3 by fastforce  
next
  case (CondTruec s b c1 c2)
  thus ?case by (simp add: cptn_mod.CptnModCondT)
next
  case (CondFalsec s b c1 c2)
  thus ?case by (simp add: cptn_mod.CptnModCondF)
next
 case (WhileTruec s1 b c)
 have sinb: "s1\<in>b" by fact
 have SeqcWhile: "(\<Gamma>, (Seq c (While b c), Normal s1) # xs) \<in> cptn_mod" by fact  
 have divseq:"(\<forall>s P Q zs. (Seq c (While b c), Normal s1) # xs=(Seq P Q, s)#zs \<longrightarrow>
                (\<exists>xs s'. ((\<Gamma>,(P, s)#xs) \<in> cptn_mod  \<and> 
                           (zs=(map (lift Q) xs) \<or>
                           ((fst(((P, s)#xs)!length xs)=Skip \<and> 
                             (\<exists>ys. (\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod \<and> 
                              zs=(map (lift (Q)) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
                           ((fst(((P, s)#xs)!length xs)=Throw \<and> 
                               snd(last ((P, s)#xs)) = Normal s' \<and>
                              (\<exists>ys.  (\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod \<and>
                      zs=(map (lift Q) xs)@((Throw,Normal s')#ys))))))                            
                 ))" using div_seq [OF SeqcWhile] by (auto simp add: seq_cond_def)
{fix sa P Q zsa
       assume ass:"(Seq c (While b c), Normal s1) # xs = (Seq P Q, sa) # zsa"
       then have eqs:"c = P \<and> (While b c) = Q \<and> Normal s1 = sa \<and> xs = zsa" by auto
       then have "(\<exists>xs s'. (\<Gamma>, (P, sa) # xs) \<in> cptn_mod \<and>
                        (zsa = map (lift Q) xs \<or>              
                         fst (((P, sa) # xs) ! length xs) = Skip \<and>
                             (\<exists>ys. (\<Gamma>, (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<in> cptn_mod \<and>
                             zsa = map (lift Q) xs @ (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<or>
                        ((fst(((P, sa)#xs)!length xs)=Throw \<and> 
                          snd(last ((P, sa)#xs)) = Normal s' \<and>
                          (\<exists>ys.  (\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod \<and>
                      zsa=(map (lift Q) xs)@((Throw,Normal s')#ys))
                        ))))" 
             using ass divseq by auto
    } note conc=this [of c "While b c" "Normal s1" xs] 
   then obtain xs' s' 
        where  split:"(\<Gamma>, (c, Normal s1) # xs') \<in> cptn_mod \<and>
     (xs = map (lift (While b c)) xs' \<or>
      fst (((c, Normal s1) # xs') ! length xs') = Skip \<and>
      (\<exists>ys. (\<Gamma>, (While b c, snd (((c, Normal s1) # xs') ! length xs')) # ys)
            \<in> cptn_mod \<and>
            xs =
            map (lift (While b c)) xs' @
            (While b c, snd (((c, Normal s1) # xs') ! length xs')) # ys) \<or>
      fst (((c, Normal s1) # xs') ! length xs') = Throw \<and>
      snd (last ((c, Normal s1) # xs')) = Normal s' \<and> 
      (\<exists>ys.  (\<Gamma>, ((Throw, Normal s')#ys)) \<in> cptn_mod \<and>
      xs = map (lift (While b c)) xs' @ ((Throw, Normal s')#ys)))"  by auto
 then have "(xs = map (lift (While b c)) xs' \<or>
            fst (((c, Normal s1) # xs') ! length xs') = Skip \<and>
            (\<exists>ys. (\<Gamma>, (While b c, snd (((c, Normal s1) # xs') ! length xs')) # ys)
                  \<in> cptn_mod \<and>
                  xs =
                  map (lift (While b c)) xs' @
                  (While b c, snd (((c, Normal s1) # xs') ! length xs')) # ys) \<or>
            fst (((c, Normal s1) # xs') ! length xs') = Throw \<and>
            snd (last ((c, Normal s1) # xs')) = Normal s' \<and>
            (\<exists>ys.  (\<Gamma>, ((Throw, Normal s')#ys)) \<in> cptn_mod \<and>
          xs = map (lift (While b c)) xs' @ ((Throw, Normal s')#ys)))" ..
 thus ?case
 proof{ 
   assume 1:"xs = map (lift (While b c)) xs'"  
   have 3:"(\<Gamma>, (c, Normal s1) # xs') \<in> cptn_mod" using split by auto   
   then show ?thesis using "1" cptn_mod.CptnModWhile1 sinb by fastforce 
 next
   assume "fst (((c, Normal s1) # xs') ! length xs') = Skip \<and>
          (\<exists>ys. (\<Gamma>, (While b c, snd (((c, Normal s1) # xs') ! length xs')) # ys)
                \<in> cptn_mod \<and>
                xs =
                map (lift (While b c)) xs' @
                (While b c, snd (((c, Normal s1) # xs') ! length xs')) # ys) \<or>
          fst (((c, Normal s1) # xs') ! length xs') = Throw \<and>
          snd (last ((c, Normal s1) # xs')) = Normal s' \<and>
          (\<exists>ys.  (\<Gamma>, ((Throw, Normal s')#ys)) \<in> cptn_mod \<and>
          xs = map (lift (While b c)) xs' @ ((Throw, Normal s')#ys))"
   thus ?case
   proof
     assume asm:"fst (((c, Normal s1) # xs') ! length xs') = Skip \<and>
             (\<exists>ys. (\<Gamma>, (While b c, snd (((c, Normal s1) # xs') ! length xs')) # ys)
             \<in> cptn_mod \<and>
             xs =
             map (lift (While b c)) xs' @
             (While b c, snd (((c, Normal s1) # xs') ! length xs')) # ys)"
     then obtain ys 
       where asm':"(\<Gamma>, (While b c, snd (last ((c, Normal s1) # xs'))) # ys)
                   \<in> cptn_mod 
                   \<and> xs = map (lift (While b c)) xs' @
                       (While b c, snd (last ((c, Normal s1) # xs'))) # ys" 
              by (auto simp add: last_length)
     moreover have 3:"(\<Gamma>, (c, Normal s1) # xs') \<in> cptn_mod" using split by auto
     moreover from asm have "fst (last ((c, Normal s1) # xs'))  = Skip"
          by (simp add: last_length) 
     ultimately show ?case using sinb by (auto simp add:CptnModWhile2)
   next
    assume asm:" fst (((c, Normal s1) # xs') ! length xs') = Throw \<and>
          snd (last ((c, Normal s1) # xs')) = Normal s' \<and>
          (\<exists>ys.  (\<Gamma>, ((Throw, Normal s')#ys)) \<in> cptn_mod \<and>
          xs = map (lift (While b c)) xs' @ ((Throw, Normal s')#ys))"   
     moreover have 3:"(\<Gamma>, (c, Normal s1) # xs') \<in> cptn_mod" using split by auto
     moreover from asm have "fst (last ((c, Normal s1) # xs'))  = Throw"
          by (simp add: last_length) 
     ultimately show ?case using sinb by (auto simp add:CptnModWhile3)
   qed
 }qed  
next
 case (WhileFalsec s b c)
 thus ?case by (simp add: cptn_mod.CptnModSkip stepc.WhileFalsec)
next
  case (Awaitc s b c t)
  thus ?case by (simp add: cptn_mod.CptnModSkip stepc.Awaitc)
next
  case (AwaitAbruptc s b c t t')
  thus ?case by (simp add: cptn_mod.CptnModThrow stepc.AwaitAbruptc) 
next
  case (Callc p bdy s)
  thus ?case by (simp add: cptn_mod.CptnModCall) 
next
  case (CallUndefinedc p s)
  thus ?case by (simp add: cptn_mod.CptnModSkip stepc.CallUndefinedc)
next
  case (DynComc c s)
  thus ?case by (simp add: cptn_mod.CptnModDynCom) 
next
  case (Catchc c1 s c1' s' c2)
   have step: "\<Gamma>\<turnstile>\<^sub>c (c1, s) \<rightarrow> (c1', s')" by (simp add: Catchc.hyps(1))
  then have nsc1: "c1\<noteq>Skip" using stepc_elim_cases(1) by blast 
  have assum: "(\<Gamma>, (Catch c1' c2, s') # xs) \<in> cptn_mod" 
  using Catchc.prems by blast
  have divcatch:"(\<forall>s P Q zs. (Catch c1' c2, s') # xs=(Catch P Q, s)#zs \<longrightarrow>
  (\<exists>xs s' s''. ((\<Gamma>,(P, s)#xs) \<in> cptn_mod  \<and> 
             (zs=(map (lift_catch Q) xs) \<or>
             ((fst(((P, s)#xs)!length xs)=Throw \<and>
               snd(last ((P, s)#xs)) = Normal s' \<and>  s=Normal s''\<and>
               (\<exists>ys. (\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod \<and> 
                zs=(map (lift_catch Q) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
                ((fst(((P, s)#xs)!length xs)=Skip \<and>  
                  (\<exists>ys. (\<Gamma>,(Skip,snd(last ((P, s)#xs)))#ys) \<in> cptn_mod \<and>                   
                 zs=(map (lift_catch Q) xs)@((Skip,snd(last ((P, s)#xs)))#ys))                
                 ))))
   ))" using div_catch [OF assum] by (auto simp add: catch_cond_def)
   {fix sa P Q zsa
       assume ass:"(Catch c1' c2, s') # xs = (Catch P Q, sa) # zsa"
       then have eqs:"c1' = P \<and> c2 = Q \<and> s' = sa \<and> xs = zsa" by auto
       then have "(\<exists>xs sv' sv''. ((\<Gamma>,(P, sa)#xs) \<in> cptn_mod  \<and> 
             (zsa=(map (lift_catch Q) xs) \<or>
             ((fst(((P, sa)#xs)!length xs)=Throw \<and>
               snd(last ((P, sa)#xs)) = Normal sv' \<and>  s'=Normal sv''\<and>
               (\<exists>ys. (\<Gamma>,(Q, snd(((P, sa)#xs)!length xs))#ys) \<in> cptn_mod \<and> 
                zsa=(map (lift_catch Q) xs)@((Q, snd(((P, sa)#xs)!length xs))#ys)))) \<or>
                ((fst(((P, sa)#xs)!length xs)=Skip \<and>                  
                 (\<exists>ys. (\<Gamma>,(Skip,snd(last ((P, sa)#xs)))#ys) \<in> cptn_mod \<and>                   
                 zsa=(map (lift_catch Q) xs)@((Skip,snd(last ((P, sa)#xs)))#ys))))))
   )"   using ass divcatch by blast
    } note conc=this [of c1' c2 s' xs]    
     then obtain xs' sa' sa''
       where split:
         "(\<Gamma>, (c1', s') # xs') \<in> cptn_mod \<and> 
          (xs = map (lift_catch c2) xs' \<or>
          fst (((c1', s') # xs') ! length xs') = Throw \<and>
          snd (last ((c1', s') # xs')) = Normal sa' \<and> s' = Normal sa'' \<and>
          (\<exists>ys. (\<Gamma>, (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<in> cptn_mod \<and>
                xs = map (lift_catch c2) xs' @
                (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<or>
          fst (((c1', s') # xs') ! length xs') = Skip \<and>
          (\<exists>ys. (\<Gamma>,(Skip,snd(last ((c1', s')#xs')))#ys) \<in> cptn_mod \<and>                   
                 xs=(map (lift_catch c2) xs')@((Skip,snd(last ((c1', s')#xs')))#ys)))"          
        by blast
  then have "(xs = map (lift_catch c2) xs' \<or>
          fst (((c1', s') # xs') ! length xs') = Throw \<and>
          snd (last ((c1', s') # xs')) = Normal sa' \<and> s' = Normal sa'' \<and>
          (\<exists>ys. (\<Gamma>, (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<in> cptn_mod \<and>
                xs = map (lift_catch c2) xs' @
                (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<or>
          fst (((c1', s') # xs') ! length xs') = Skip \<and>
          (\<exists>ys. (\<Gamma>,(Skip,snd(last ((c1', s')#xs')))#ys) \<in> cptn_mod \<and>                   
                 xs=(map (lift_catch c2) xs')@((Skip,snd(last ((c1', s')#xs')))#ys)))"          
        by auto
  thus ?case 
  proof{           
       assume c1'nonf:"xs = map (lift_catch c2) xs'"
       then have c1'cptn:"(\<Gamma>, (c1', s') # xs') \<in> cptn_mod" using split by blast
       then have induct_step: "(\<Gamma>, (c1, s) # (c1', s')#xs') \<in> cptn_mod"
         using Catchc.hyps(2)  by blast
       then have "(Catch c1' c2, s')#xs = map (lift_catch c2) ((c1', s')#xs')"
            using c1'nonf
            by (simp add: CptnModCatch1 lift_catch_def)
       thus ?thesis 
            using c1'nonf c1'cptn induct_step by (auto simp add: CptnModCatch1)
    next
      assume "fst (((c1', s') # xs') ! length xs') = Throw \<and>
                snd (last ((c1', s') # xs')) = Normal sa' \<and> s' = Normal sa'' \<and>
                (\<exists>ys. (\<Gamma>, (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<in> cptn_mod \<and>
                xs =map (lift_catch c2) xs' @ (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<or>
               fst (((c1', s') # xs') ! length xs') = Skip \<and>
                (\<exists>ys. (\<Gamma>,(Skip,snd(last ((c1', s')#xs')))#ys) \<in> cptn_mod \<and>                   
                 xs=(map (lift_catch c2) xs')@((Skip,snd(last ((c1', s')#xs')))#ys))"  
      thus ?thesis
      proof
         assume assth:
               "fst (((c1', s') # xs') ! length xs') = Throw \<and>
                snd (last ((c1', s') # xs')) = Normal sa' \<and> s' = Normal sa'' \<and>
                (\<exists>ys. (\<Gamma>, (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<in> cptn_mod \<and>
                xs =map (lift_catch c2) xs' @ (c2, snd (((c1', s') # xs') ! length xs')) # ys)"
             then have s'eqsa'': "s'=Normal sa''" by auto
             then have snormal: "\<exists>ns. s=Normal ns" by (metis Catchc.hyps(1) step_Abrupt_prop step_Fault_prop step_Stuck_prop xstate.exhaust)
             then obtain ys 
             where split':"(\<Gamma>, (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<in> cptn_mod \<and>
                xs =map (lift_catch c2) xs' @ (c2, snd (((c1', s') # xs') ! length xs')) # ys"
                using assth by auto    
         then have c1'cptn:"(\<Gamma>, (c1', s') # xs') \<in> cptn_mod" 
              using split by blast
         then have induct_step: "(\<Gamma>, (c1, s) # (c1', s')#xs') \<in> cptn_mod"
              using Catchc.hyps(2)  by blast                
         then have seqmap:"(Catch c1 c2, s)#(Catch c1' c2, s')#xs = map (lift_catch c2) ((c1,s)#(c1', s')#xs') @ (c2, snd (((c1', s') # xs') ! length xs')) # ys"
              using split' by (simp add: CptnModCatch3 lift_catch_def) 
        then have lastc1:"last ((c1, s) # (c1', s') # xs') = ((c1', s') # xs') ! length xs'"
             by (simp add: last_length) 
        then have lastc1skip:"fst (last ((c1, s) # (c1', s') # xs')) = Throw" 
             using assth by fastforce
        then have "snd (last ((c1, s) # (c1', s') # xs')) = Normal sa'"
             using assth by force
        thus ?thesis using snormal seqmap s'eqsa'' split' last_length  cptn_mod.CptnModCatch3 induct_step lastc1 lastc1skip
             by fastforce 
    next
        assume assm:" fst (((c1', s') # xs') ! length xs') = Skip \<and> 
                       (\<exists>ys. (\<Gamma>,(Skip,snd(last ((c1', s')#xs')))#ys) \<in> cptn_mod \<and>                   
                      xs=(map (lift_catch c2) xs')@((Skip,snd(last ((c1', s')#xs')))#ys))"
        then have c1'cptn:"(\<Gamma>, (c1', s') # xs') \<in> cptn_mod" using split by blast
        then have induct_step: "(\<Gamma>, (c1, s) # (c1', s')#xs') \<in> cptn_mod"
        using Catchc.hyps(2)  by blast 
        then have "map (lift_catch c2) ((c1', s') # xs') = (Catch c1' c2, s') # map (lift_catch c2) xs'" 
          by (auto simp add: lift_catch_def)
        then obtain ys 
             where seqmap:"(Catch c1' c2, s')#xs = (map (lift_catch c2) ((c1', s')#xs'))@((Skip,snd(last ((c1', s')#xs')))#ys)"
        using assm by fastforce
        then have lastc1:"last ((c1, s) # (c1', s') # xs') = ((c1', s') # xs') ! length xs'"
                   by (simp add: last_length) 
        then have lastc1skip:"fst (last ((c1, s) # (c1', s') # xs')) = Skip" 
             using assm by fastforce
        then have "snd (last ((c1, s) # (c1', s') # xs')) = snd (last ((c1', s') # xs'))"
             using assm by force
        thus ?thesis 
            using assm c1'cptn induct_step lastc1skip seqmap by (auto simp add:cptn_mod.CptnModCatch2)
    qed
  }qed              
next
  case (CatchThrowc c2 s)
  have c2incptn:"(\<Gamma>, (c2, Normal s) # xs) \<in> cptn_mod" by fact
  then have 1:"(\<Gamma>, [(Throw, Normal s)]) \<in> cptn_mod" by (simp add: cptn_mod.CptnModOne)
  then have 2:"fst(last ([(Throw, Normal s)])) = Throw" by fastforce
  then have 3:"(\<Gamma>,(c2, snd(last [(Throw, Normal s)]))#xs) \<in> cptn_mod" 
      using c2incptn by auto  
  then have "(c2,Normal s)#xs=(map (lift c2) [])@(c2, snd(last [(Throw, Normal s)]))#xs" 
       by (auto simp add:lift_def)
  thus ?case using 1 2 3 by (simp add: CptnModCatch3)
next
  case (CatchSkipc c2 s)
  have "(\<Gamma>, [(Skip, s)]) \<in> cptn_mod" by (simp add: cptn_mod.CptnModOne)
  then obtain ys where ys_nil:"ys=[]" and last:"(\<Gamma>, (Skip,  s)#ys)\<in> cptn_mod"
    by auto
  moreover have "fst (last ((Skip,  s)#ys)) = Skip" using ys_nil last by auto
  moreover have "snd (last ((Skip,  s)#ys)) = s" using ys_nil last by auto
  moreover from ys_nil have "(map (lift_catch c2) ys) = []" by auto  
  ultimately show ?case using CatchSkipc.prems by simp (simp add: cptn_mod.CptnModCatch2 ys_nil)
next
  case (FaultPropc c f)
  thus ?case by (simp add: cptn_mod.CptnModSkip stepc.FaultPropc) 
next
  case (AbruptPropc c f)
  thus ?case by (simp add: cptn_mod.CptnModSkip stepc.AbruptPropc)
next
  case (StuckPropc c)
  thus ?case by (simp add: cptn_mod.CptnModSkip stepc.StuckPropc)
qed

lemma cptn_onlyif_cptn_mod: 
assumes cptn_asm:"(\<Gamma>,c) \<in> cptn"
shows  "(\<Gamma>,c) \<in> cptn_mod"
using cptn_asm
proof (induct) 
 case CptnOne thus ?case by (rule CptnModOne)
next
 case (CptnEnv \<Gamma> P t xs s) thus ?case by (simp add: cptn_mod.CptnModEnv) 
next
 case CptnComp thus ?case
 by (simp add: cptn_onlyif_cptn_mod_aux)
qed

lemma lift_is_cptn: 
assumes cptn_asm:"(\<Gamma>,c)\<in>cptn"
shows "(\<Gamma>,map (lift P) c) \<in> cptn"
using cptn_asm
proof (induct)
 case CptnOne thus ?case using cptn.simps by fastforce
next
  case (CptnEnv \<Gamma> P s t xs) thus ?case 
      by (cases rule:step_e.cases, 
          (simp add: cptn.CptnEnv step_e.Env lift_def), 
          (simp add: cptn.CptnEnv step_e.Env_n lift_def))
next                                              
  case CptnComp thus ?case by (simp add: Seqc cptn.CptnComp lift_def)
qed

lemma lift_catch_is_cptn:
assumes cptn_asm:"(\<Gamma>,c)\<in>cptn"
shows "(\<Gamma>,map (lift_catch P) c) \<in> cptn"
using cptn_asm
proof (induct)
  case CptnOne thus ?case using cptn.simps by fastforce
next
  case CptnEnv thus ?case  by (cases rule:step_e.cases, 
          (simp add: cptn.CptnEnv step_e.Env lift_catch_def), 
          (simp add: cptn.CptnEnv step_e.Env_n lift_catch_def))
next
  case CptnComp thus ?case by (simp add: Catchc cptn.CptnComp lift_catch_def)
qed

lemma last_lift: "\<lbrakk>xs\<noteq>[]; fst(xs!(length xs - (Suc 0)))=Q\<rbrakk> 
 \<Longrightarrow> fst((map (lift P) xs)!(length (map (lift P) xs)- (Suc 0)))=Seq Q P"
  by (cases "(xs ! (length xs - (Suc 0)))") (simp add:lift_def)

lemma last_lift_catch: "\<lbrakk>xs\<noteq>[]; fst(xs!(length xs - (Suc 0)))=Q\<rbrakk> 
 \<Longrightarrow> fst((map (lift_catch P) xs)!(length (map (lift_catch P) xs)- (Suc 0)))=Catch Q P"
  by (cases "(xs ! (length xs - (Suc 0)))") (simp add:lift_catch_def)

lemma last_fst [rule_format]: "P((a#x)!length x) \<longrightarrow> \<not>P a \<longrightarrow> P (x!(length x - (Suc 0)))" 
  by (induct x) simp_all


lemma last_fst_esp: 
 "fst(((P,s)#xs)!(length xs))=Skip \<Longrightarrow> P\<noteq>Skip \<Longrightarrow> fst(xs!(length xs - (Suc 0)))=Skip" 
apply(erule last_fst)
apply simp
done

lemma last_snd: "xs\<noteq>[] \<Longrightarrow> 
  snd(((map (lift P) xs))!(length (map (lift P) xs) - (Suc 0)))=snd(xs!(length xs - (Suc 0)))"
  by (cases "(xs ! (length xs - (Suc 0)))") (simp_all add:lift_def)

lemma last_snd_catch: "xs\<noteq>[] \<Longrightarrow> 
  snd(((map (lift_catch P) xs))!(length (map (lift_catch P) xs) - (Suc 0)))=snd(xs!(length xs - (Suc 0)))"
  by (cases "(xs ! (length xs - (Suc 0)))") (simp_all add:lift_catch_def)

lemma Cons_lift: "((Seq P Q), s) # (map (lift Q) xs) = map (lift Q) ((P, s) # xs)"
  by (simp add:lift_def)
thm last_map eq_snd_iff list.inject list.simps(9) last_length
lemma Cons_lift_catch: "((Catch P Q), s) # (map (lift_catch Q) xs) = map (lift_catch Q) ((P, s) # xs)"
  by (simp add:lift_catch_def)

lemma Cons_lift_append: 
  "((Seq P Q), s) # (map (lift Q) xs) @ ys = map (lift Q) ((P, s) # xs)@ ys "
  by (simp add:lift_def)

lemma Cons_lift_catch_append: 
  "((Catch P Q), s) # (map (lift_catch Q) xs) @ ys = map (lift_catch Q) ((P, s) # xs)@ ys "
  by (simp add:lift_catch_def)

lemma lift_nth: "i<length xs \<Longrightarrow> map (lift Q) xs ! i = lift Q  (xs! i)"
  by (simp add:lift_def)

lemma lift_catch_nth: "i<length xs \<Longrightarrow> map (lift_catch Q) xs ! i = lift_catch Q  (xs! i)"
  by (simp add:lift_catch_def)
thm list.simps(9) last_length lift_catch_def Cons_lift_catch
lemma snd_lift: "i< length xs \<Longrightarrow> snd(lift Q (xs ! i))= snd (xs ! i)"
  by (cases "xs!i") (simp add:lift_def)

lemma snd_lift_catch: "i< length xs \<Longrightarrow> snd(lift_catch Q (xs ! i))= snd (xs ! i)"
  by (cases "xs!i") (simp add:lift_catch_def)

lemma Normal_Normal: 
assumes p1:"(\<Gamma>, (P, Normal s) # a # as) \<in> cptn" and       
        p2:"(\<exists>sb. snd (last ((P, Normal s) # a # as))  = Normal sb)"
shows "\<exists>sa. snd a = Normal sa"
proof -
   obtain la1 la2 where last_prod:"last ((P, Normal s)# a#as) = (la1,la2)" by fastforce
   obtain a1 a2 where a_prod:"a=(a1,a2)" by fastforce
   from p1 have clos_p_a:"\<Gamma>\<turnstile>\<^sub>c (P,Normal s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (a1, a2)" using a_prod cptn_elim_cases(2)
    proof -
      have f1: "(\<Gamma>, (P, Normal s) # (a1, a2) # as) \<in> cptn"
        using a_prod p1 by fastforce
      have "last [(a1, a2)] = (a1, a2)"
        by auto
      thus ?thesis
        using f1 by (metis (no_types) cptn_dest1 cptn_stepconf_rtrancl last_ConsR not_Cons_self2)
    qed  
   then have "\<Gamma>\<turnstile>\<^sub>c (fst a, snd a) \<rightarrow>\<^sub>c\<^sub>e\<^sup>*  (la1,la2)"
   proof -
     from p1 have "(\<Gamma>,(a # as)) \<in> cptn" using a_prod cptn_dest by blast
     thus ?thesis by (metis cptn_stepconf_rtrancl last_ConsR last_prod list.distinct(1) prod.collapse) 
   qed 
   then obtain bb where "Normal bb = la2" using last_prod p2 by auto
   thus ?thesis by (metis (no_types) `\<Gamma>\<turnstile>\<^sub>c (fst a, snd a) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (la1, la2)` steps_ce_not_Normal)
qed
  

lemma lift_P1: 
 assumes map_cptn:"(\<Gamma>, map (lift Q) ((P, s) # xs)) \<in> cptn" and
         P_ends:"fst (last ((P, s) # xs)) = Skip"
 shows "(\<Gamma>, map (lift Q) ((P, s) # xs) @ [(Q, snd (last ((P, s) # xs)))]) \<in> cptn"
using map_cptn P_ends
proof (induct xs arbitrary: P s) 
  case Nil
  have P0_skips: "P=Skip" using Nil.prems(2) by auto   
  have "(\<Gamma>,[(Seq Skip Q, s), (Q, s)]) \<in> cptn"
    by (simp add: cptn.CptnComp SeqSkipc cptn.CptnOne)
  then show ?case using P0_skips by (simp add: lift_def)
next
  case (Cons a xs)
  have "(\<Gamma>, map (lift Q) ((P, s) # a # xs)) \<in> cptn"
    using Cons.prems(1) by blast  
  have "fst (last ( a # xs)) = Skip" using Cons.prems(2) by auto
  also have seq_PQ:"(\<Gamma>,(Seq P Q,s) # (map (lift Q) (a#xs))) \<in> cptn"
    by (metis Cons.prems(1) Cons_lift)
  then have "(\<Gamma>,(map (lift Q) (a#xs))) \<in> cptn"
    proof -
      assume a1:"(\<Gamma>, (Seq P Q, s) # map (lift Q) (a # xs)) \<in> cptn"            
      then obtain a1 a2 xs1 where a2: "map (lift Q) (a#xs) = ((a1,a2)#xs1)" by fastforce 
      thus ?thesis  using cptn_dest using seq_PQ by auto 
    qed 
  then have "(\<Gamma>, map (lift Q) (a#xs) @ [(Q, snd (last ((a#xs))))]) \<in> cptn" 
   by (metis Cons.hyps(1) calculation prod.collapse)   
  then have t1:"(\<Gamma>, (Seq (fst a) Q, (snd a))#map (lift Q) xs @ [(Q, snd (last ((P, s)#(a#xs))))]) \<in> cptn"
   by (simp add: Cons_lift_append)
  then have "(\<Gamma>,(Seq P Q,s) # (Seq (fst a) Q, (snd a))#map (lift Q) xs)\<in> cptn"
   using seq_PQ by (simp add: Cons_lift)  
  then have t2: "(\<Gamma>,(Seq P Q,s) # [(Seq (fst a) Q, (snd a))]) \<in> cptn"
   using cptn_dest1 by blast
  then have"((Seq P Q,s) # [(Seq (fst a) Q, (snd a))])!length [(Seq (fst a) Q, (snd a))] = (Seq (fst a) Q, (snd a))"
   by auto  
  then have "(\<Gamma>,(Seq P Q,s) # [(Seq (fst a) Q, (snd a))]@map (lift Q) xs @ [(Q, snd (last ((P, s)#(a#xs))))])\<in> cptn"
   using cptn_append_is_cptn t1 t2 by blast   
  then have "(\<Gamma>, map (lift Q) ((P,s)#(fst a, snd a)#xs) @[(Q, snd (last ((P, s)#(a#xs))))])\<in>cptn"
   using Cons_lift_append append_Cons append_Nil by metis
  thus ?case by auto    
qed


lemma lift_catch_P1: 
 assumes map_cptn:"(\<Gamma>, map (lift_catch Q) ((P, Normal s) # xs)) \<in> cptn" and
         P_ends:"fst (last ((P, Normal s) # xs)) = Throw" and
         P_ends_normal:"\<exists>p. snd(last ((P, Normal s) # xs)) = Normal p"
 shows "(\<Gamma>, map (lift_catch Q) ((P, Normal s) # xs) @ [(Q, snd (last ((P, Normal s) # xs)))]) \<in> cptn"
using map_cptn P_ends P_ends_normal
proof (induct xs arbitrary: P s) 
  case Nil
  have P0_skips: "P=Throw" using Nil.prems(2) by auto   
  have "(\<Gamma>,[(Catch Throw Q, Normal s), (Q, Normal s)]) \<in> cptn"
    by (simp add: cptn.CptnComp CatchThrowc cptn.CptnOne)
  then show ?case using P0_skips by (simp add: lift_catch_def)
next
  case (Cons a xs) 
  have s1:"(\<Gamma>, map (lift_catch Q) ((P, Normal s) # a # xs)) \<in> cptn"
    using Cons.prems(1) by blast 
  have s2:"fst (last ( a # xs)) = Throw" using Cons.prems(2) by auto
  then obtain p where s3:"snd(last (a #xs)) = Normal p" using Cons.prems(3) by auto
  also have seq_PQ:"(\<Gamma>,(Catch P Q,Normal s) # (map (lift_catch Q) (a#xs))) \<in> cptn"
    by (metis Cons.prems(1) Cons_lift_catch) thm Cons.hyps
  then have axs_in_cptn:"(\<Gamma>,(map (lift_catch Q) (a#xs))) \<in> cptn"
    proof -
      assume a1:"(\<Gamma>, (Catch P Q, Normal s) # map (lift_catch Q) (a # xs)) \<in> cptn"            
      then obtain a1 a2 xs1 where a2: "map (lift_catch Q) (a#xs) = ((a1,a2)#xs1)" by fastforce 
      thus ?thesis  using cptn_dest using seq_PQ by auto 
    qed 
  then have "(\<Gamma>, map (lift_catch Q) (a#xs) @ [(Q, snd (last ((a#xs))))]) \<in> cptn" 
    proof (cases "xs=[]")
      case True thus ?thesis using s2 s3 axs_in_cptn by (metis Cons.hyps eq_snd_iff last_ConsL)
    next
      case False            
      from seq_PQ have seq:"(\<Gamma>,(Catch P Q,Normal s) # (Catch (fst a) Q,snd a)#map (lift_catch Q) xs)\<in> cptn"
        by (simp add: Cons_lift_catch)                         
      obtain cf sf where last_map_axs:"(cf,sf)=last (map (lift_catch Q) (a#xs))" using prod.collapse by blast
      have "\<forall>p ps. (ps=[] \<and> last [p] = p) \<or> (ps\<noteq>[] \<and> last (p#ps) = last ps)" by simp              
      then have tranclos:"\<Gamma>\<turnstile>\<^sub>c (Catch P Q,Normal s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (Catch (fst a) Q,snd a)" using Cons_lift_catch
            by (metis (no_types) cptn_dest1 cptn_stepc_rtrancl not_Cons_self2 seq)
      have tranclos_a:"\<Gamma>\<turnstile>\<^sub>c (Catch (fst a) Q,snd a) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (cf,sf)"
           by (metis Cons_lift_catch axs_in_cptn cptn_stepc_rtrancl last_map_axs prod.collapse)      
      have snd_last:"snd (last (map (lift_catch Q) (a#xs))) = snd (last (a #xs))"
      proof - 
         have eqslist:"snd(((map (lift_catch Q) (a#xs)))!(length (map (lift_catch Q) xs)))= snd((a#xs)!(length xs))" 
           using last_snd_catch by fastforce  
         have "(lift_catch Q a)#(map (lift_catch Q) xs) = (map (lift_catch Q) (a#xs))" by auto
         then have "(map (lift_catch Q) (a#xs))!(length (map (lift_catch Q) xs)) = last (map (lift_catch Q) (a#xs))"
           using last_length [of "(lift_catch Q a)" "(map (lift_catch Q) xs)"] by auto
         thus ?thesis using eqslist by (simp add:last_length)
      qed
      then obtain p1 where  "(snd a) = Normal p1"
         by (metis tranclos_a last_map_axs s3 snd_conv step_ce_normal_to_normal tranclos)   
      moreover obtain a1 a2 where aeq:"a = (a1,a2)" by fastforce 
      moreover have "fst (last ((a1,a2) # xs)) = Throw" using s2 False by auto  
      moreover have "(\<Gamma>, map (lift_catch Q) ((a1,a2) # xs)) \<in> cptn" using aeq axs_in_cptn False by auto  
      moreover have "\<exists>p. snd (last ((a1,a2) # xs)) = Normal p" using s3 aeq by auto
      moreover have "a2 = Normal p1" using aeq calculation(1) by auto 
      ultimately have "(\<Gamma>, map (lift_catch Q) ((a1,a2) # xs) @
                           [(Q, snd (last ((a1,a2) # xs)))])\<in> cptn" 
                 using Cons.hyps aeq by blast
      thus ?thesis using aeq by force 
    qed      
  then have t1:"(\<Gamma>, (Catch (fst a) Q, (snd a))#map (lift_catch Q) xs @ [(Q, snd (last ((P, Normal s)#(a#xs))))]) \<in> cptn"
   by (simp add: Cons_lift_catch_append)
  then have "(\<Gamma>,(Catch P Q,Normal s) # (Catch (fst a) Q, (snd a))#map (lift_catch Q) xs)\<in> cptn"
   using seq_PQ by (simp add: Cons_lift_catch)  
  then have t2: "(\<Gamma>,(Catch P Q,Normal s) # [(Catch (fst a) Q, (snd a))]) \<in> cptn"
   using cptn_dest1 by blast
  then have"((Catch P Q,Normal s) # [(Catch (fst a) Q, (snd a))])!length [(Catch (fst a) Q, (snd a))] = (Catch (fst a) Q, (snd a))"
   by auto  
  then have "(\<Gamma>,(Catch P Q,Normal s) # [(Catch (fst a) Q, (snd a))]@map (lift_catch Q) xs @ [(Q, snd (last ((P, Normal s)#(a#xs))))])\<in> cptn"
   using cptn_append_is_cptn t1 t2 by blast
  then have "(\<Gamma>, map (lift_catch Q) ((P,Normal s)#(fst a, snd a)#xs) @[(Q, snd (last ((P,Normal s)#(a#xs))))])\<in>cptn"
   using Cons_lift_catch_append append_Cons append_Nil by metis
  thus ?case by auto    
qed

lemma seq2:
assumes 
    p1:"(\<Gamma>, (P0, s) # xs) \<in> cptn_mod" and
    p2:"(\<Gamma>, (P0, s) # xs) \<in> cptn" and
    p3:"fst (last ((P0, s) # xs)) = Skip" and
    p4:"(\<Gamma>, (P1, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod" and
    p5:"(\<Gamma>, (P1, snd (last ((P0, s) # xs))) # ys) \<in> cptn" and
    p6:"zs = map (lift P1) xs @ (P1, snd (last ((P0, s) # xs))) # ys"
shows "(\<Gamma>, (Seq P0 P1, s) # zs) \<in> cptn"
using p1 p2 p3 p4 p5 p6
proof -
have last_skip:"fst (last ((P0, s) # xs)) = Skip" using p3 by blast 
  have "(\<Gamma>, (map (lift P1) ((P0, s) # xs))@(P1, snd (last ((P0, s) # xs))) # ys) \<in> cptn"
  proof -
    have "(\<Gamma>,map (lift P1) ((P0, s) #xs)) \<in> cptn"
      using p2 lift_is_cptn by blast 
    then have "(\<Gamma>,map (lift P1) ((P0, s) #xs)@[(P1, snd (last ((P0, s) # xs)))]) \<in> cptn" 
      using last_skip lift_P1 by blast 
    then have "(\<Gamma>,(Seq P0 P1, s) # map (lift P1) xs@[(P1, snd (last ((P0, s) # xs)))]) \<in> cptn"
         by (simp add: Cons_lift_append)
    moreover have "last ((Seq P0 P1, s) # map (lift P1) xs @[(P1, snd (last ((P0, s) # xs)))]) = (P1, snd (last ((P0, s) # xs)))" 
      by auto  
    moreover have "last ((Seq P0 P1, s) # map (lift P1) xs @[(P1, snd (last ((P0, s) # xs)))]) =
                   ((Seq P0 P1, s) # map (lift P1) xs @[(P1, snd (last ((P0, s) # xs)))])!length (map (lift P1) xs @[(P1, snd (last ((P0, s) # xs)))])" 
      by (metis last_length)             
    ultimately have "(\<Gamma>, (Seq P0 P1, s) # map (lift P1) xs @ (P1, snd (last ((P0, s) # xs))) # ys)\<in> cptn" 
      using cptn_append_is_cptn p5 by fastforce
    thus ?thesis by (simp add: Cons_lift_append)
  qed 
  thus ?thesis  
    by (simp add: Cons_lift_append p6)
qed

lemma seq3:
assumes
    p1:"(\<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod" and
    p2:"(\<Gamma>, (P0, Normal s) # xs) \<in> cptn" and
    p3:"fst (last ((P0, Normal s) # xs)) = Throw" and
    p4:"snd (last ((P0, Normal s) # xs)) = Normal s'" and
    p5:"(\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod" and
    p6:"(\<Gamma>,(Throw,Normal s')#ys) \<in> cptn" and
    p7:"zs = map (lift P1) xs @((Throw,Normal s')#ys)" 
shows "(\<Gamma>, (Seq P0 P1, Normal s) # zs) \<in> cptn"
using p1 p2 p3 p4 p5 p6 p7
proof (induct xs arbitrary: zs P0 s) 
  case Nil thus ?case using SeqThrowc cptn.simps by fastforce
next
  case (Cons a as)
  then obtain sa where "snd a = Normal sa" by (meson Normal_Normal)
  obtain a1 a2 where a_prod:"a=(a1,a2)" by fastforce
  obtain la1 la2 where last_prod:"last (a#as) = (la1,la2)" by fastforce 
  then have lasst_aas_last: "last (a#as) = (last ((P0, Normal s) # a # as))" by auto    
  then have "la1 = Throw" using Cons.prems(3) last_prod by force
  have "la2 = Normal s'" using Cons.prems(4) last_prod lasst_aas_last by force
  have f1: "(\<Gamma>, (a1, a2) # as) \<in> cptn"
    using Cons.prems(2) a_prod cptn_dest by blast
  have f2: "Normal sa = a2"
    using `snd a = Normal sa` a_prod by force
  have "(\<Gamma>, a # as) \<in> cptn_mod"
    using f1 a_prod cptn_onlyif_cptn_mod by blast
  then have hyp:"(\<Gamma>, (Seq a1 P1, Normal sa) # 
            map (lift P1) as @ ((Throw,Normal s')#ys)) \<in> cptn"
        using Cons.hyps Cons.prems(3) Cons.prems(4)  Cons.prems(5) Cons.prems(6) a_prod f1 f2 by fastforce
  thus ?case
  proof -
    have "(Seq a1 P1, a2) # map (lift P1) as @((Throw,Normal s')#ys) = zs"
      by (simp add: Cons.prems(7) Cons_lift_append a_prod)
    thus ?thesis
      by (metis (no_types, lifting) Cons.prems(2) Seqc a_prod cptn.CptnComp cptn.CptnEnv Env cptn_elim_cases(2) f2 hyp)     
  qed 
qed

lemma cptn_if_cptn_mod: 
assumes cptn_mod_asm:"(\<Gamma>,c) \<in> cptn_mod"
shows  "(\<Gamma>,c) \<in> cptn"
using cptn_mod_asm
proof (induct)
  case (CptnModOne) thus ?case using cptn.CptnOne by blast
next
  case CptnModSkip thus ?case by (simp add: cptn.CptnComp) 
next
  case CptnModThrow thus ?case by (simp add: cptn.CptnComp) 
next 
  case CptnModCondT thus ?case by (simp add: CondTruec cptn.CptnComp) 
next
  case CptnModCondF thus ?case by (simp add: CondFalsec cptn.CptnComp)
next
  case (CptnModSeq1 \<Gamma> P0 s xs zs P1) 
  have "(\<Gamma>, map (lift P1) ((P0, s) # xs)) \<in> cptn"
    using CptnModSeq1.hyps(2) lift_is_cptn by blast
  thus ?case by (simp add: Cons_lift CptnModSeq1.hyps(3))
next
  case (CptnModSeq2 \<Gamma> P0 s xs P1 ys zs)   
  thus ?case by (simp add:seq2)
next
  case (CptnModSeq3 \<Gamma> P0 s xs s' zs P1) 
  thus ?case by (simp add: seq3)
next
  case (CptnModWhile1  \<Gamma> P s xs b zs) thus ?case by (metis Cons_lift WhileTruec cptn.CptnComp lift_is_cptn)
next 
  case (CptnModWhile2  \<Gamma> P s xs b zs ys)    
  then have "(\<Gamma>, (Seq P (While b P), Normal s) # zs) \<in> cptn" 
    by (simp add:seq2)  
  then have "\<Gamma>\<turnstile>\<^sub>c(While b P,Normal s) \<rightarrow> (Seq P (While b P),Normal s)" 
    by (simp add: CptnModWhile2.hyps(4) WhileTruec)
  thus ?case
   by (simp add: `(\<Gamma>, (Seq P (While b P), Normal s) # zs) \<in> cptn` cptn.CptnComp) 
next
  case (CptnModWhile3  \<Gamma> P s xs b s' ys zs) 
  then have "(\<Gamma>,(Seq P (While b P), Normal s) # zs) \<in> cptn"
     by (simp add: seq3)     
  then have "\<Gamma>\<turnstile>\<^sub>c(While b P,Normal s) \<rightarrow> (Seq P (While b P),Normal s)" by (simp add: CptnModWhile3.hyps(4) WhileTruec)
  thus ?case by (simp add: `(\<Gamma>, (Seq P (While b P), Normal s) # zs) \<in> cptn` cptn.CptnComp)
next 
  case (CptnModCall \<Gamma> bdy s ys p) thus ?case by (simp add: Callc cptn.CptnComp) 
next
  case (CptnModDynCom \<Gamma> c s ys) thus ?case by (simp add: DynComc cptn.CptnComp)
next
  case (CptnModGuard \<Gamma> c s ys g f) thus ?case by (simp add: Guardc cptn.CptnComp)
next
  case (CptnModCatch1 \<Gamma> P0 s xs zs P1)
  have "(\<Gamma>, map (lift_catch P1) ((P0, s) # xs)) \<in> cptn"
    using CptnModCatch1.hyps(2) lift_catch_is_cptn by blast
  thus ?case by (simp add: Cons_lift_catch CptnModCatch1.hyps(3))
next
  case (CptnModCatch2 \<Gamma> P0 s xs ys zs P1)
  thus ?case
  proof (induct xs arbitrary: zs P0 s) 
    case Nil thus ?case using CatchSkipc cptn.simps by fastforce
  next
    case (Cons a as)
    then obtain sa where "snd a = sa" by auto
    then obtain a1 a2 where a_prod:"a=(a1,a2)" and sa_a2: "a2 =sa" 
           by fastforce
    obtain la1 la2 where last_prod:"last (a#as) = (la1,la2)" by fastforce 
    then have lasst_aas_last: "last (a#as) = (last ((P0, s) # a # as))" by auto    
    then have "la1 = Skip" using Cons.prems(3) last_prod by force
    have f1: "(\<Gamma>, (a1, a2) # as) \<in> cptn"
      using Cons.prems(2) a_prod cptn_dest by blast
    have "(\<Gamma>, a # as) \<in> cptn_mod"
      using f1 a_prod cptn_onlyif_cptn_mod by blast
    then have hyp:"(\<Gamma>, (Catch a1 P1, a2) # 
              map (lift_catch P1) as @ ((Skip, la2)#ys)) \<in> cptn"
          using Cons.hyps Cons.prems a_prod f1 last_prod by fastforce
    thus ?case
    proof -
      have f1:"(Catch a1 P1, a2) # map (lift_catch P1) as @ ((Skip, la2)#ys) = zs"
        using Cons.prems(4) Cons_lift_catch_append a_prod last_prod by (simp add: Cons.prems(6))         
      have "(\<Gamma>, map (lift_catch P1) ((P0, s) # a # as)) \<in> cptn"
       using Cons.prems(2) lift_catch_is_cptn by blast
      hence "(\<Gamma>, (LanguageCon.com.Catch P0 P1, s) # (LanguageCon.com.Catch a1 P1, a2) # map (lift_catch P1) as) \<in> cptn"
        by (metis (no_types) Cons_lift_catch a_prod)
      hence "(\<Gamma>, (LanguageCon.com.Catch P0 P1, s) # zs) \<in> cptn \<or> (\<Gamma>, (LanguageCon.com.Catch P0 P1, s) # (LanguageCon.com.Catch a1 P1, a2) # map (lift_catch P1) as) \<in> cptn \<and> (\<not> \<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Catch P0 P1, s) \<rightarrow>\<^sub>e (LanguageCon.com.Catch P0 P1, a2) \<or> (\<Gamma>, (LanguageCon.com.Catch P0 P1, a2) # map (lift_catch P1) as) \<notin> cptn \<or> LanguageCon.com.Catch a1 P1 \<noteq> LanguageCon.com.Catch P0 P1)"
        using f1 cptn.CptnEnv hyp by blast
      thus ?thesis
       by (metis (no_types) f1 cptn.CptnComp cptn_elim_cases(2) hyp)
     qed
   qed
next 
  case (CptnModCatch3  \<Gamma> P0 s xs s' P1 ys zs)
  thus ?case
  proof (induct xs arbitrary: zs P0 s) 
    case Nil thus ?case using CatchThrowc cptn.simps by fastforce
  next
    case (Cons a as)
    then obtain sa where "snd a = Normal sa" by (meson Normal_Normal)
    obtain a1 a2 where a_prod:"a=(a1,a2)" by fastforce
    obtain la1 la2 where last_prod:"last (a#as) = (la1,la2)" by fastforce 
    then have lasst_aas_last: "last (a#as) = (last ((P0, Normal s) # a # as))" by auto    
    then have "la1 = Throw" using Cons.prems(3) last_prod by force
    have "la2 = Normal s'" using Cons.prems(4) last_prod lasst_aas_last by force
    have f1: "(\<Gamma>, (a1, a2) # as) \<in> cptn"
      using Cons.prems(2) a_prod cptn_dest by blast
    have f2: "Normal sa = a2"
      using `snd a = Normal sa` a_prod by force
    have "(\<Gamma>, a # as) \<in> cptn_mod"
      using f1 a_prod cptn_onlyif_cptn_mod by blast
    then have hyp:"(\<Gamma>, (Catch a1 P1, Normal sa) # 
              map (lift_catch P1) as @ (P1, snd (last ((a1, Normal sa) # as))) # ys) \<in> cptn"
          using Cons.hyps Cons.prems a_prod f1 f2 by auto
    thus ?case
    proof -
      have "\<Gamma>\<turnstile>\<^sub>c (P0, Normal s) \<rightarrow>\<^sub>e (P0, a2)"
        by (fastforce intro: step_e.intros)
      then have transit:"\<Gamma>\<turnstile>\<^sub>c(P0,Normal s) \<rightarrow>\<^sub>c\<^sub>e (a1,Normal sa)" 
            by (metis (no_types) Cons.prems(2) a_prod c_step cptn_elim_cases(2) e_step f2)
      then have transit_catch:"\<Gamma>\<turnstile>\<^sub>c(Catch P0 P1,Normal s) \<rightarrow>\<^sub>c\<^sub>e (Catch a1 P1,Normal sa)"
            by (metis (no_types) Catchc c_step e_step env_c_c' step_ce_elim_cases step_e.intros(1)) 
      have "(Catch a1 P1, a2) # map (lift_catch P1) as @ (P1, la2) # ys = zs"
        using Cons.prems Cons_lift_catch_append a_prod last_prod by auto        
      have "a=(a1, Normal sa)" using a_prod f2 by auto
      have "snd (last ((a1, Normal sa) # as)) = Normal s'"
          using `a = (a1, Normal sa)` `snd (last ((P0, Normal s) # a # as)) = Normal s'` lasst_aas_last by fastforce
      hence f1: "snd (last ((a1, Normal sa) # as)) = la2"
          using `la2 = Normal s'` by blast
      have "\<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Catch P0 P1, Normal s) \<rightarrow>\<^sub>c\<^sub>e (LanguageCon.com.Catch a1 P1, a2)"
          using f2 transit_catch by blast
      thus ?thesis
        using f1 `(LanguageCon.com.Catch a1 P1, a2) # map (lift_catch P1) as @ (P1, la2) # ys = zs`  
              cptn.CptnComp cptn.CptnEnv f2 hyp not_eq_not_env step_ce_not_step_e_step_c 
        by metis
    qed
  qed
next 
  case (CptnModEnv) thus ?case by (simp add: cptn.CptnEnv)
qed

lemma cptn_eq_cptn_mod: 
shows  "(x \<in>cptn_mod)  = (x\<in>cptn)"
by (cases x, auto simp add: cptn_if_cptn_mod cptn_onlyif_cptn_mod)

lemma cptn_eq_cptn_mod_set: 
shows  "cptn_mod  = cptn"
by (auto simp add: cptn_if_cptn_mod cptn_onlyif_cptn_mod)

subsection \<open>Computational modular semantic for nested calls\<close>
inductive_set cptn_mod_nest_call :: "(nat\<times>('s,'p,'f,'e) confs) set"
where
  CptnModNestOne: "(n,\<Gamma>,[(P, s)]) \<in> cptn_mod_nest_call"
| CptnModNestEnv: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow>\<^sub>e (P,t);(n,\<Gamma>,(P, t)#xs) \<in> cptn_mod_nest_call\<rbrakk> \<Longrightarrow> 
                     (n,\<Gamma>,(P, s)#(P, t)#xs) \<in> cptn_mod_nest_call"
| CptnModNestSkip: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow> (Skip,t); redex P = P; 
                     \<forall>f. ((\<exists>sn. s = Normal sn) \<and> (\<Gamma> f) = Some Skip \<longrightarrow> P  \<noteq> Call f  );
                (n,\<Gamma>,(Skip, t)#xs) \<in> cptn_mod_nest_call \<rbrakk> \<Longrightarrow> 
                (n,\<Gamma>,(P,s)#(Skip, t)#xs) \<in>cptn_mod_nest_call"

| CptnModNestThrow: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow> (Throw,t); redex P = P; 
                     \<forall>f. ((\<exists>sn. s = Normal sn) \<and> (\<Gamma> f) = Some Throw \<longrightarrow> P  \<noteq> Call f  );
                      (n,\<Gamma>,(Throw, t)#xs) \<in> cptn_mod_nest_call \<rbrakk> \<Longrightarrow> 
                      (n,\<Gamma>,(P,s)#(Throw, t)#xs) \<in>cptn_mod_nest_call"

| CptnModNestCondT: "\<lbrakk>(n,\<Gamma>,(P0, Normal s)#ys) \<in> cptn_mod_nest_call; s \<in> b \<rbrakk> \<Longrightarrow> 
                    (n,\<Gamma>,((Cond b P0 P1), Normal s)#(P0, Normal s)#ys) \<in> cptn_mod_nest_call"

| CptnModNestCondF: "\<lbrakk>(n,\<Gamma>,(P1, Normal s)#ys) \<in> cptn_mod_nest_call; s \<notin> b \<rbrakk> \<Longrightarrow> 
                     (n,\<Gamma>,((Cond b P0 P1), Normal s)#(P1, Normal s)#ys) \<in> cptn_mod_nest_call"

| CptnModNestSeq1: 
  "\<lbrakk>(n,\<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call; zs=map (lift P1) xs \<rbrakk> \<Longrightarrow> 
   (n,\<Gamma>,((Seq P0 P1), s)#zs) \<in> cptn_mod_nest_call"

| CptnModNestSeq2: 
  "\<lbrakk>(n,\<Gamma>, (P0, s)#xs) \<in> cptn_mod_nest_call; fst(last ((P0, s)#xs)) = Skip;
    (n,\<Gamma>,(P1, snd(last ((P0, s)#xs)))#ys) \<in> cptn_mod_nest_call;
    zs=(map (lift P1) xs)@((P1, snd(last ((P0, s)#xs)))#ys) \<rbrakk> \<Longrightarrow> 
   (n,\<Gamma>,((Seq P0 P1), s)#zs) \<in> cptn_mod_nest_call"

| CptnModNestSeq3: 
  "\<lbrakk>(n,\<Gamma>, (P0, Normal s)#xs) \<in> cptn_mod_nest_call; 
    fst(last ((P0, Normal s)#xs)) = Throw;
    snd(last ((P0, Normal s)#xs)) = Normal s'; 
    (n,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call; 
    zs=(map (lift P1) xs)@((Throw,Normal s')#ys) \<rbrakk> \<Longrightarrow>
   (n,\<Gamma>,((Seq P0 P1), Normal s)#zs) \<in> cptn_mod_nest_call"

| CptnModNestWhile1: 
  "\<lbrakk>(n,\<Gamma>, (P, Normal s)#xs) \<in> cptn_mod_nest_call; s \<in> b; 
    zs=map (lift (While b P)) xs \<rbrakk> \<Longrightarrow> 
    (n,\<Gamma>, ((While b P), Normal s)#
      ((Seq P (While b P)),Normal s)#zs) \<in> cptn_mod_nest_call"

| CptnModNestWhile2: 
  "\<lbrakk> (n,\<Gamma>, (P, Normal s)#xs) \<in> cptn_mod_nest_call; 
     fst(last ((P, Normal s)#xs))=Skip; s \<in> b; 
     zs=(map (lift (While b P)) xs)@
      (While b P, snd(last ((P, Normal s)#xs)))#ys; 
      (n,\<Gamma>,(While b P, snd(last ((P, Normal s)#xs)))#ys) \<in> 
        cptn_mod_nest_call\<rbrakk> \<Longrightarrow> 
   (n,\<Gamma>,(While b P, Normal s)#
     (Seq P (While b P), Normal s)#zs) \<in> cptn_mod_nest_call"

| CptnModNestWhile3: 
  "\<lbrakk> (n,\<Gamma>, (P, Normal s)#xs) \<in> cptn_mod_nest_call; 
     fst(last ((P, Normal s)#xs))=Throw; s \<in> b;
     snd(last ((P, Normal s)#xs)) = Normal s'; 
    (n,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call;  
     zs=(map (lift (While b P)) xs)@((Throw,Normal s')#ys)\<rbrakk> \<Longrightarrow> 
   (n,\<Gamma>,(While b P, Normal s)#
     (Seq P (While b P), Normal s)#zs) \<in> cptn_mod_nest_call"

| CptnModNestCall: "\<lbrakk>(n,\<Gamma>,(bdy, Normal s)#ys) \<in> cptn_mod_nest_call;\<Gamma> p = Some bdy; bdy\<noteq>Call p \<rbrakk> \<Longrightarrow> 
                 (Suc n, \<Gamma>,((Call p), Normal s)#(bdy, Normal s)#ys) \<in> cptn_mod_nest_call" 

| CptnModNestDynCom: "\<lbrakk>(n,\<Gamma>,(c s, Normal s)#ys) \<in> cptn_mod_nest_call \<rbrakk> \<Longrightarrow> 
                 (n,\<Gamma>,(DynCom c, Normal s)#(c s, Normal s)#ys) \<in> cptn_mod_nest_call"

| CptnModNestGuard: "\<lbrakk>(n,\<Gamma>,(c, Normal s)#ys) \<in> cptn_mod_nest_call; s \<in> g \<rbrakk> \<Longrightarrow> 
                  (n,\<Gamma>,(Guard f g c, Normal s)#(c, Normal s)#ys) \<in> cptn_mod_nest_call"

| CptnModNestCatch1: "\<lbrakk>(n,\<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call; zs=map (lift_catch P1) xs \<rbrakk>
                 \<Longrightarrow> (n,\<Gamma>,((Catch P0 P1), s)#zs) \<in> cptn_mod_nest_call"

| CptnModNestCatch2: 
  "\<lbrakk>(n,\<Gamma>, (P0, s)#xs) \<in> cptn_mod_nest_call; fst(last ((P0, s)#xs)) = Skip; 
    (n,\<Gamma>,(Skip,snd(last ((P0, s)#xs)))#ys) \<in> cptn_mod_nest_call;  
    zs=(map (lift_catch P1) xs)@((Skip,snd(last ((P0, s)#xs)))#ys) \<rbrakk> \<Longrightarrow> 
   (n,\<Gamma>,((Catch P0 P1), s)#zs) \<in> cptn_mod_nest_call"

| CptnModNestCatch3: 
  "\<lbrakk>(n,\<Gamma>, (P0, Normal s)#xs) \<in> cptn_mod_nest_call; fst(last ((P0, Normal s)#xs)) = Throw; 
  snd(last ((P0, Normal s)#xs)) = Normal s';
  (n,\<Gamma>,(P1, snd(last ((P0, Normal s)#xs)))#ys) \<in> cptn_mod_nest_call; 
  zs=(map (lift_catch P1) xs)@((P1, snd(last ((P0, Normal s)#xs)))#ys) \<rbrakk> \<Longrightarrow> 
   (n,\<Gamma>,((Catch P0 P1), Normal s)#zs) \<in> cptn_mod_nest_call"

lemmas CptnMod_nest_call_induct = cptn_mod_nest_call.induct [of _ _ "[(c,s)]", split_format (complete), case_names
CptnModOne CptnModEnv CptnModSkip CptnModThrow CptnModCondT CptnModCondF 
CptnModSeq1 CptnModSeq2 CptnModSeq3 CptnModSeq4 CptnModWhile1 CptnModWhile2 CptnModWhile3 CptnModCall CptnModDynCom CptnModGuard 
CptnModCatch1 CptnModCatch2 CptnModCatch3, induct set]

inductive_cases CptnModNest_elim_cases [cases set]:
"(n,\<Gamma>,(Skip, s)#u#xs) \<in> cptn_mod_nest_call"
"(n,\<Gamma>,(Guard f g c, s)#u#xs) \<in> cptn_mod_nest_call"
"(n,\<Gamma>,(Basic f e, s)#u#xs) \<in> cptn_mod_nest_call"
"(n,\<Gamma>,(Spec r e, s)#u#xs) \<in> cptn_mod_nest_call"
"(n,\<Gamma>,(Seq c1 c2, s)#u#xs) \<in> cptn_mod_nest_call"
"(n,\<Gamma>,(Cond b c1 c2, s)#u#xs) \<in> cptn_mod_nest_call"
"(n,\<Gamma>,(Await b c2 e, s)#u#xs) \<in> cptn_mod_nest_call"
"(n,\<Gamma>,(Call p, s)#u#xs) \<in> cptn_mod_nest_call"
"(n,\<Gamma>,(DynCom c,s)#u#xs) \<in> cptn_mod_nest_call"
"(n,\<Gamma>,(Throw,s)#u#xs) \<in> cptn_mod_nest_call"
"(n,\<Gamma>,(Catch c1 c2,s)#u#xs) \<in> cptn_mod_nest_call"

inductive_cases stepc_elim_cases_Seq_Seq':
"\<Gamma>\<turnstile>\<^sub>c(Seq c1 c2,s) \<rightarrow> (Seq c1' c2',s')" 

inductive_cases stepc_elim_cases_Catch_Catch':
"\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> (Catch c1' c2',s')" 

inductive_cases CptnModNest_same_elim_cases [cases set]:
"(n,\<Gamma>,(u, s)#(u,t)#xs) \<in> cptn_mod_nest_call"

inductive_cases CptnModNest_elim_cases_Stuck [cases set]:
"(n,\<Gamma>,(P, Stuck)#(Skip, s)#xs) \<in> cptn_mod_nest_call"

inductive_cases CptnModNest_elim_cases_Fault [cases set]:
"(n,\<Gamma>,(P, Fault f)#(Skip, s)#xs) \<in> cptn_mod_nest_call"

inductive_cases CptnModNest_elim_cases_Abrupt [cases set]:
"(n,\<Gamma>,(P, Abrupt as)#(Skip, s)#xs) \<in> cptn_mod_nest_call"

inductive_cases  CptnModNest_elim_cases_Call_Stuck [cases set]:
"(n,\<Gamma>,(Call p, s)#(Skip, Stuck)#xs) \<in> cptn_mod_nest_call"

inductive_cases  CptnModNest_elim_cases_Call [cases set]:
"(0, \<Gamma>,((Call p), Normal s)#(bdy, Normal s)#ys) \<in> cptn_mod_nest_call"

inductive_cases  CptnEmpty [cases set]:
"(n, \<Gamma>,[]) \<in> cptn_mod_nest_call"

inductive_cases  CptnModNest_elim_cases_Call_normal [cases set]:
"(Suc n, \<Gamma>,((Call p), Normal s)#(bdy, Normal s)#ys) \<in> cptn_mod_nest_call"

lemma cptn_mod_nest_mono1: "(n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call  \<Longrightarrow> (Suc n,\<Gamma>,cfs)\<in> cptn_mod_nest_call"
proof (induct rule:cptn_mod_nest_call.induct)
  case (CptnModNestOne) thus ?case using cptn_mod_nest_call.CptnModNestOne by auto
next
  case (CptnModNestEnv) thus ?case using cptn_mod_nest_call.CptnModNestEnv by fastforce
next
   case (CptnModNestSkip) thus ?case using cptn_mod_nest_call.CptnModNestSkip by fastforce
next
   case (CptnModNestThrow) thus ?case using cptn_mod_nest_call.intros(4)  by fastforce
next
   case (CptnModNestCondT n) thus ?case 
     using cptn_mod_nest_call.CptnModNestCondT[of "Suc n"] by fastforce
next
  case (CptnModNestCondF n) thus ?case 
    using cptn_mod_nest_call.CptnModNestCondF[of "Suc n"] by fastforce
next
  case (CptnModNestSeq1 n) thus ?case 
    using cptn_mod_nest_call.CptnModNestSeq1[of "Suc n"] by fastforce
next
  case (CptnModNestSeq2 n) thus ?case 
     using cptn_mod_nest_call.CptnModNestSeq2[of "Suc n"] by fastforce
next
  case (CptnModNestSeq3 n) thus ?case 
     using cptn_mod_nest_call.CptnModNestSeq3[of "Suc n"] by fastforce
next
  case (CptnModNestWhile1 n) thus ?case 
     using cptn_mod_nest_call.CptnModNestWhile1[of "Suc n"] by fastforce
next
  case (CptnModNestWhile2 n) thus ?case 
     using cptn_mod_nest_call.CptnModNestWhile2[of "Suc n"] by fastforce
next
  case (CptnModNestWhile3 n) thus ?case 
     using cptn_mod_nest_call.CptnModNestWhile3[of "Suc n"] by fastforce
next
 case (CptnModNestCall) thus ?case 
     using cptn_mod_nest_call.CptnModNestCall by fastforce
next 
 case (CptnModNestDynCom) thus ?case 
     using cptn_mod_nest_call.CptnModNestDynCom by fastforce
next
 case (CptnModNestGuard n) thus ?case 
     using cptn_mod_nest_call.CptnModNestGuard[of "Suc n"] by fastforce
next
 case (CptnModNestCatch1 n) thus ?case 
     using cptn_mod_nest_call.CptnModNestCatch1[of "Suc n"] by fastforce
next
 case (CptnModNestCatch2 n) thus ?case 
     using cptn_mod_nest_call.CptnModNestCatch2[of "Suc n"] by fastforce
next
 case (CptnModNestCatch3 n) thus ?case 
     using cptn_mod_nest_call.CptnModNestCatch3[of "Suc n"] by fastforce
qed

lemma cptn_mod_nest_mono2: 
  "(n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call  \<Longrightarrow> m>n \<Longrightarrow>
   (m,\<Gamma>,cfs)\<in> cptn_mod_nest_call"
proof (induct "m-n" arbitrary: m n)
  case 0 thus ?case by auto
next
  case (Suc k) 
  have "m - Suc n = k"
    using Suc.hyps(2) Suc.prems(2) Suc_diff_Suc Suc_inject by presburger
  then show ?case
    using Suc.hyps(1) Suc.prems(1) Suc.prems(2) cptn_mod_nest_mono1 less_Suc_eq by blast   
qed

lemma cptn_mod_nest_mono: 
  "(n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call  \<Longrightarrow> m\<ge>n \<Longrightarrow>
   (m,\<Gamma>,cfs)\<in> cptn_mod_nest_call"
proof (cases "n=m")
  assume "(n, \<Gamma>, cfs) \<in> cptn_mod_nest_call" and  
          "n = m"  thus ?thesis by auto
next
  assume "(n, \<Gamma>, cfs) \<in> cptn_mod_nest_call" and  
         "n\<le>m" and
         "n \<noteq> m"  
   thus ?thesis by (auto simp add: cptn_mod_nest_mono2)
qed

subsection \<open>Lemmas on normalization\<close>

(* lemma step_sequence_flatten:
  assumes exec: "\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow> (Q,t)" 
  shows "\<Gamma>\<turnstile>\<^sub>c(sequence Seq (flatten P),s) \<rightarrow> (sequence Seq (flatten Q),t)"
using exec
proof (induct rule: stepc_induct)
  case (Guardc s g f c) thus ?case using stepc.Guardc
  case (Seqc c1 s c2 s' c2')
  then have " \<Gamma>\<turnstile>\<^sub>c (Seq (LanguageCon.sequence LanguageCon.com.Seq (LanguageCon.flatten c1)) c2', s) \<rightarrow>
                   (Seq (LanguageCon.sequence LanguageCon.com.Seq (LanguageCon.flatten c2)) c2', s') " 
    using stepc.Seqc by fastforce    
  thus ?case sorry
qed(auto intro:stepc.intros)+

lemma normalice_step:
  assumes exec:"\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow> (Q,t)" 
  shows  "\<Gamma>\<turnstile>\<^sub>c( normalizec P,s) \<rightarrow> (normalizec Q,t)"
using exec
proof(induct rule:stepc_induct)
  case (Catchc P s Q t c2)
    thus ?case
   *) 
(* qed(auto intro: stepc.intros) *)

subsection \<open>Equivalence of comp mod semantics and comp mod nested\<close>

definition catch_cond_nest
where
"catch_cond_nest zs Q xs P s s'' s' \<Gamma> n \<equiv> (zs=(map (lift_catch Q) xs) \<or>
             ((fst(((P, s)#xs)!length xs)=Throw \<and>
               snd(last ((P, s)#xs)) = Normal s' \<and> s=Normal s''\<and>
               (\<exists>ys. (n,\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod_nest_call \<and> 
                zs=(map (lift_catch Q) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
                ((fst(((P, s)#xs)!length xs)=Skip \<and> 
                 (\<exists>ys. (n,\<Gamma>,(Skip,snd(last ((P, s)#xs)))#ys) \<in> cptn_mod_nest_call \<and>                   
                 zs=(map (lift_catch Q) xs)@((Skip,snd(last ((P, s)#xs)))#ys)))))
"

lemma div_catch_nest: assumes cptn_m:"(n,\<Gamma>,list) \<in> cptn_mod_nest_call"
shows "(\<forall>s P Q zs. list=(Catch P Q, s)#zs \<longrightarrow>
       (\<exists>xs s' s''. 
          (n, \<Gamma>,(P, s)#xs) \<in> cptn_mod_nest_call  \<and> 
             catch_cond_nest zs Q xs P s s'' s' \<Gamma> n))  
            "
unfolding catch_cond_nest_def
using cptn_m
proof (induct rule: cptn_mod_nest_call.induct)
case (CptnModNestOne \<Gamma> P s)
  thus ?case using cptn_mod_nest_call.CptnModNestOne by blast 
next
  case (CptnModNestSkip  \<Gamma> P s t n xs) 
  from CptnModNestSkip.hyps
  have step: "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow> (Skip, t)" by auto
  from CptnModNestSkip.hyps
  have noskip: "~(P=Skip)" using stepc_elim_cases(1) by blast  
  have no_catch: "\<forall>p1 p2. \<not>(P=Catch p1 p2)" using CptnModNestSkip.hyps(2) redex_not_Catch by auto
  from CptnModNestSkip.hyps
  have in_cptn_mod: "(n,\<Gamma>, (Skip, t) # xs) \<in> cptn_mod_nest_call" by auto  
  then show ?case using no_catch by simp
next
  case (CptnModNestThrow  \<Gamma> P s t n xs) 
  from CptnModNestThrow.hyps
  have step: "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow> (Throw, t)" by auto 
  from CptnModNestThrow.hyps
  have in_cptn_mod: "(n,\<Gamma>, (Throw, t) # xs) \<in> cptn_mod_nest_call" by auto 
  have no_catch: "\<forall>p1 p2. \<not>(P=Catch p1 p2)" using CptnModNestThrow.hyps(2) redex_not_Catch by auto
  then show ?case by auto
next
  case (CptnModNestCondT \<Gamma> P0 s ys b P1)
  thus ?case using CptnModOne by blast
next
  case (CptnModNestCondF \<Gamma> P0 s ys b P1)
  thus ?case using CptnModOne by blast
next
  case (CptnModNestCatch1 sa P Q zs)
  thus ?case by blast
next
  case (CptnModNestCatch2 n \<Gamma> P0 s xs ys zs P1) 
  from CptnModNestCatch2.hyps(3) 
  have last:"fst (((P0, s) # xs) ! length xs) = Skip" 
       by (simp add: last_length) 
  have P0cptn:"(n,\<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call" by fact          
  then have "zs = map (lift_catch P1) xs @((Skip,snd(last ((P0, s)#xs)))#ys)" by (simp add:CptnModNestCatch2.hyps)
  show ?case
  proof -{
    fix sa P Q zsa    
    assume eq:"(Catch P0 P1, s) # zs = (Catch P Q, sa) # zsa"
    then have "P0 =P \<and> P1 = Q \<and> s=sa \<and> zs=zsa" by auto
    then have "(P0, s) = (P, sa)" by auto 
    have "last ((P0, s) # xs) = ((P, sa) # xs) ! length xs"
      by (simp add: `P0 = P \<and> P1 = Q \<and> s = sa \<and> zs = zsa` last_length)
    then have "zs = (map (lift_catch Q) xs)@((Skip,snd(last ((P0, s)#xs)))#ys)"
      using `P0 = P \<and> P1 = Q \<and> s = sa \<and> zs = zsa` `zs = map (lift_catch P1) xs @ ((Skip,snd(last ((P0, s)#xs)))#ys)` 
      by force    
    then have "(\<exists>xs s' s''. ((n,\<Gamma>,(P, s)#xs) \<in> cptn_mod_nest_call  \<and> 
             ((zs=(map (lift_catch Q) xs) \<or>
             ((fst(((P, s)#xs)!length xs)=Throw \<and>
               snd(last ((P, s)#xs)) = Normal s' \<and>  s=Normal s''\<and>
               (\<exists>ys. (n,\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod_nest_call \<and> 
                zs=(map (lift_catch Q) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
                (\<exists>ys. ((fst(((P, s)#xs)!length xs)=Skip \<and> (n,\<Gamma>,(Skip,snd(last ((P, s)#xs)))#ys) \<in> cptn_mod_nest_call \<and>                 
                 zs=(map (lift_catch Q) xs)@((Skip,snd(last ((P0, s)#xs)))#ys))))))))"
    using P0cptn  `P0 = P \<and> P1 = Q \<and> s = sa \<and> zs = zsa`  last  CptnModNestCatch2.hyps(4) by blast 
   } 
   thus ?thesis by auto
  qed
next
  case (CptnModNestCatch3 n \<Gamma> P0 s xs s' P1 ys zs)
  from CptnModNestCatch3.hyps(3)  
  have last:"fst (((P0, Normal s) # xs) ! length xs) = Throw" 
       by (simp add: last_length) 
  from CptnModNestCatch3.hyps(4) 
  have lastnormal:"snd (last ((P0, Normal s) # xs)) = Normal s'"
      by (simp add: last_length)
  have P0cptn:"(n,\<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod_nest_call" by fact
  from CptnModNestCatch3.hyps(5) 
    have P1cptn:"(n,\<Gamma>, (P1, snd (((P0, Normal s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call"
      by (simp add: last_length)          
  then have "zs = map (lift_catch P1) xs @ (P1, snd (last ((P0, Normal s) # xs))) # ys" 
    by (simp add:CptnModNestCatch3.hyps)
  show ?case
  proof -{
    fix sa P Q zsa    
    assume eq:"(Catch P0 P1, Normal s) # zs = (Catch P Q, Normal sa) # zsa"
    then have "P0 =P \<and> P1 = Q \<and> Normal s= Normal sa \<and> zs=zsa" by auto     
    have "last ((P0, Normal s) # xs) = ((P, Normal sa) # xs) ! length xs"
      by (simp add: `P0 = P \<and> P1 = Q \<and> Normal s = Normal sa \<and> zs = zsa` last_length)
    then have "zsa = map (lift_catch Q) xs @ (Q, snd (((P, Normal sa) # xs) ! length xs)) # ys"
      using `P0 = P \<and> P1 = Q \<and> Normal s = Normal sa \<and> zs = zsa` `zs = map (lift_catch P1) xs @ (P1, snd (last ((P0, Normal s) # xs))) # ys` by force
    then have "(n,\<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call \<and> (fst(((P, Normal s)#xs)!length xs)=Throw \<and>
               snd(last ((P, Normal s)#xs)) = Normal s' \<and> 
              (\<exists>ys. (n,\<Gamma>,(Q, snd(((P, Normal s)#xs)!length xs))#ys) \<in> cptn_mod_nest_call \<and> 
              zs=(map (lift_catch Q) xs)@((Q, snd(((P, Normal s)#xs)!length xs))#ys)))" 
      using lastnormal P1cptn P0cptn `P0 = P \<and> P1 = Q \<and> Normal s = Normal sa \<and> zs = zsa` last 
       by auto    
    }note this [of P0 P1 s zs] thus ?thesis by blast qed
next
  case (CptnModNestEnv \<Gamma> P s t n xs)  
  then have step:"(n, \<Gamma>, (P, t) # xs) \<in> cptn_mod_nest_call" by auto  
  have step_e: "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow>\<^sub>e (P, t)" using CptnModNestEnv by auto
  show ?case     
    proof (cases P)
      case (Catch P1 P2) 
      then have eq_P_Catch:"(P, t) # xs = (LanguageCon.com.Catch P1 P2, t) # xs" by auto      
      then  obtain xsa t' t'' where 
         p1:"(n,\<Gamma>, (P1, t) # xsa) \<in> cptn_mod_nest_call" and 
        p2:" (xs = map (lift_catch P2) xsa \<or>
            fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Throw \<and>
            snd (last ((P1, t) # xsa)) = Normal t' \<and>
            t = Normal t'' \<and>
            (\<exists>ys. (n,\<Gamma>, (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<in> cptn_mod_nest_call \<and>
              xs = map (lift_catch P2) xsa @ (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<or>
                fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Skip \<and>
                (\<exists>ys.(n,\<Gamma>,(Skip,snd(last ((P1, t)#xsa)))#ys) \<in> cptn_mod_nest_call \<and> 
                xs = map (lift_catch P2) xsa @
                ((LanguageCon.com.Skip, snd (last ((P1, t) # xsa)))#ys)))" 
        using CptnModNestEnv(3) by auto
      have all_step:"(n,\<Gamma>, (P1, s)#((P1, t) # xsa)) \<in> cptn_mod_nest_call"
        using p1 Env Env_n cptn_mod.CptnModEnv env_normal_s step_e
      proof -
        have f1: "SmallStepCon.redex P = SmallStepCon.redex P1"
          using local.Catch by auto
        obtain bb :: "('b, 'c) xstate \<Rightarrow> 'b" where
          "\<forall>x2. (\<exists>v5. x2 = Normal v5) = (x2 = Normal (bb x2))"
          by moura
        then have "s = t \<or> s = Normal (bb s)"
          by (metis (no_types) env_normal_s step_e)
        then show ?thesis
          using f1 by (metis (no_types) Env Env_n cptn_mod_nest_call.CptnModNestEnv p1)
      qed
      show ?thesis using p2 
      proof  
        assume "xs = map (lift_catch P2) xsa"
        have "(P, t) # xs = map (lift_catch P2) ((P1, t) # xsa)"
          by (simp add: `xs = map (lift_catch P2) xsa` lift_catch_def local.Catch)
        thus ?thesis using all_step eq_P_Catch by fastforce
      next 
        assume 
         "fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Throw \<and>
          snd (last ((P1, t) # xsa)) = Normal t' \<and>
          t = Normal t'' \<and>
          (\<exists>ys. (n,\<Gamma>, (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<in> cptn_mod_nest_call \<and>
                xs =
                map (lift_catch P2) xsa @
                (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<or>
                fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Skip \<and>
           (\<exists>ys. (n,\<Gamma>,(Skip,snd(last ((P1, t)#xsa)))#ys) \<in> cptn_mod_nest_call \<and> 
            xs = map (lift_catch P2) xsa @
            ((LanguageCon.com.Skip, snd (last ((P1, t) # xsa)))#ys))"      
         then show ?thesis 
         proof
           assume 
            a1:"fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Throw \<and>
             snd (last ((P1, t) # xsa)) = Normal t' \<and>
             t = Normal t'' \<and>
             (\<exists>ys. (n,\<Gamma>, (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<in> cptn_mod_nest_call \<and>
                xs = map (lift_catch P2) xsa @
                       (P2, snd (((P1, t) # xsa) ! length xsa)) # ys)"
            then obtain ys where p2_exec:"(n,\<Gamma>, (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<in> cptn_mod_nest_call \<and>
                xs = map (lift_catch P2) xsa @
                       (P2, snd (((P1, t) # xsa) ! length xsa)) # ys" 
            by fastforce
            from a1 obtain t1 where t_normal: "t=Normal t1" 
              using env_normal_s'_normal_s by blast
            have f1:"fst (((P1, s)#(P1, t) # xsa) ! length ((P1, t)#xsa)) = LanguageCon.com.Throw"
              using a1 by fastforce
             from a1 have last_normal: "snd (last ((P1, s)#(P1, t) # xsa)) = Normal t'"
               by fastforce 
             then have p2_long_exec: "(n,\<Gamma>, (P2, snd (((P1, s)#(P1, t) # xsa) ! length ((P1, s)#xsa))) # ys) \<in> cptn_mod_nest_call \<and>
                (P, t)#xs = map (lift_catch P2) ((P1, t) # xsa) @
                       (P2, snd (((P1, s)#(P1, t) # xsa) ! length ((P1, s)#xsa))) # ys" using p2_exec 
                by (simp add: lift_catch_def local.Catch)                  
             thus ?thesis using  a1 f1 last_normal all_step eq_P_Catch 
               by (clarify, metis (no_types) list.size(4) not_step_c_env  step_e)            
           next
           assume 
            as1:"fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Skip \<and>
           (\<exists>ys. (n,\<Gamma>,(Skip,snd(last ((P1, t)#xsa)))#ys) \<in> cptn_mod_nest_call \<and> 
            xs = map (lift_catch P2) xsa @
            ((LanguageCon.com.Skip, snd (last ((P1, t) # xsa)))#ys))"               
            then obtain ys where p1:"(n,\<Gamma>,(Skip,snd(last ((P1, t)#xsa)))#ys) \<in> cptn_mod_nest_call \<and> 
                         (P, t)#xs = map (lift_catch P2) ((P1, t) # xsa) @
                          ((LanguageCon.com.Skip, snd (last ((P1, t) # xsa)))#ys)"
            proof -
              assume a1: "\<And>ys. (n,\<Gamma>, (LanguageCon.com.Skip, snd (last ((P1, t) # xsa))) # ys) \<in> cptn_mod_nest_call \<and> 
                         (P, t) # xs = map (lift_catch P2) ((P1, t) # xsa) @ 
                         (LanguageCon.com.Skip, snd (last ((P1, t) # xsa))) # ys \<Longrightarrow> 
                         thesis"
              have "(LanguageCon.com.Catch P1 P2, t) # map (lift_catch P2) xsa = map (lift_catch P2) ((P1, t) # xsa)"
                by (simp add: lift_catch_def)
              thus ?thesis
                using a1 as1 eq_P_Catch by moura
            qed            
            from as1 have p2: "fst (((P1, s)#(P1, t) # xsa) ! length ((P1, t) #xsa)) = LanguageCon.com.Skip"
                 by fastforce                              
            thus ?thesis using p1 all_step eq_P_Catch by fastforce
          qed
      qed
    qed (auto)
qed(force+)


definition seq_cond_nest
where
"seq_cond_nest zs Q xs P s s'' s' \<Gamma> n \<equiv> (zs=(map (lift Q) xs) \<or>
             ((fst(((P, s)#xs)!length xs)=Skip \<and> 
               (\<exists>ys. (n,\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod_nest_call \<and> 
                zs=(map (lift (Q)) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
             ((fst(((P, s)#xs)!length xs)=Throw \<and> 
                 snd(last ((P, s)#xs)) = Normal s' \<and>  s=Normal s''\<and>
                 (\<exists>ys.  (n,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call \<and>
                      zs=(map (lift Q) xs)@((Throw,Normal s')#ys)))))
"

lemma div_seq_nest: assumes cptn_m:"(n,\<Gamma>,list) \<in> cptn_mod_nest_call"
shows "(\<forall>s P Q zs. list=(Seq P Q, s)#zs \<longrightarrow>
       (\<exists>xs s' s''. 
          (n,\<Gamma>,(P, s)#xs) \<in> cptn_mod_nest_call  \<and> 
             seq_cond_nest zs Q xs P s s'' s' \<Gamma> n))  
            "
unfolding seq_cond_nest_def
using cptn_m
proof (induct rule: cptn_mod_nest_call.induct)
  case (CptnModNestOne \<Gamma> P s)
  thus ?case using cptn_mod_nest_call.CptnModNestOne 
   by blast
next
  case (CptnModNestSkip  \<Gamma> P s t n xs) 
  from CptnModNestSkip.hyps
  have step: "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow> (Skip, t)" by auto
  from CptnModNestSkip.hyps
  have noskip: "~(P=Skip)" using stepc_elim_cases(1) by blast  
  have x: "\<forall>c c1 c2. redex c = Seq c1 c2 \<Longrightarrow> False"
          using redex_not_Seq by blast
  from CptnModNestSkip.hyps
  have in_cptn_mod: "(n,\<Gamma>, (Skip, t) # xs) \<in> cptn_mod_nest_call" by auto  
  then show ?case using CptnModNestSkip.hyps(2) SmallStepCon.redex_not_Seq by blast
next
  case (CptnModNestThrow  \<Gamma> P s t xs)
  from CptnModNestThrow.hyps
  have step: "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow> (Throw, t)" by auto 
  moreover from CptnModNestThrow.hyps 
  have no_seq: "\<forall>p1 p2. \<not>(P=Seq p1 p2)" using CptnModNestThrow.hyps(2) redex_not_Seq by auto
  ultimately show ?case by auto   
next 
  case (CptnModNestCondT \<Gamma> P0 s ys b P1)
  thus ?case by auto
next
  case (CptnModNestCondF \<Gamma> P0 s ys b P1)
  thus ?case by auto
next
  case (CptnModNestSeq1 n \<Gamma> P0 s xs zs P1) thus ?case 
    by blast   
next 
  case (CptnModNestSeq2 n \<Gamma> P0 s xs P1 ys zs) 
  from CptnModNestSeq2.hyps(3) last_length have last:"fst (((P0, s) # xs) ! length xs) = Skip" 
       by (simp add: last_length) 
  have P0cptn:"(n,\<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call" by fact
  from CptnModNestSeq2.hyps(4) have P1cptn:"(n,\<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call"
      by (simp add: last_length)          
  then have "zs = map (lift P1) xs @ (P1, snd (last ((P0, s) # xs))) # ys" by (simp add:CptnModNestSeq2.hyps)
  show ?case
  proof -{
    fix sa P Q zsa    
    assume eq:"(Seq P0 P1, s) # zs = (Seq P Q, sa) # zsa"
    then have "P0 =P \<and> P1 = Q \<and> s=sa \<and> zs=zsa" by auto 
     have "last ((P0, s) # xs) = ((P, sa) # xs) ! length xs"
            by (simp add: `P0 = P \<and> P1 = Q \<and> s = sa \<and> zs = zsa` last_length)
    then have "zsa = map (lift Q) xs @ (Q, snd (((P, sa) # xs) ! length xs)) # ys"
         using `P0 = P \<and> P1 = Q \<and> s = sa \<and> zs = zsa` `zs = map (lift P1) xs @ (P1, snd (last ((P0, s) # xs))) # ys` 
         by force    
    then have "(\<exists>xs s' s''. (n,\<Gamma>, (P, sa) # xs) \<in> cptn_mod_nest_call \<and>
                        (zsa = map (lift Q) xs \<or>              
                         fst (((P, sa) # xs) ! length xs) = Skip \<and>
                             (\<exists>ys. (n,\<Gamma>, (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
                             zsa = map (lift Q) xs @ (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<or>
                        ((fst(((P, sa)#xs)!length xs)=Throw \<and> 
                          snd(last ((P, sa)#xs)) = Normal s' \<and>  s=Normal s''\<and>
                         (\<exists>ys. (n,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call \<and>
                               zsa=(map (lift Q) xs)@((Throw,Normal s')#ys))))))
               " 
        using P0cptn P1cptn  `P0 = P \<and> P1 = Q \<and> s = sa \<and> zs = zsa` last 
        by blast                 
   }  
   thus ?case by auto qed     
next
  case (CptnModNestSeq3 n \<Gamma> P0 s xs s' ys zs P1) 
  from CptnModNestSeq3.hyps(3) 
  have last:"fst (((P0, Normal s) # xs) ! length xs) = Throw" 
       by (simp add: last_length) 
  have P0cptn:"(n,\<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod_nest_call" by fact
  from CptnModNestSeq3.hyps(4) 
  have lastnormal:"snd (last ((P0, Normal s) # xs)) = Normal s'"
      by (simp add: last_length)          
  then have "zs = map (lift P1) xs @ ((Throw, Normal s')#ys)" by (simp add:CptnModNestSeq3.hyps)
  show ?case
  proof -{
    fix sa P Q zsa    
    assume eq:"(Seq P0 P1, Normal s) # zs = (Seq P Q, Normal sa) # zsa"
    then have "P0 =P \<and> P1 = Q \<and> Normal s=Normal sa \<and> zs=zsa" by auto
    then have "(P0, Normal s) = (P, Normal sa)" by auto 
    have "last ((P0, Normal s) # xs) = ((P, Normal sa) # xs) ! length xs"
                    by (simp add: `P0 = P \<and> P1 = Q \<and> Normal s = Normal sa \<and> zs = zsa` last_length)
    then have zsa:"zsa = (map (lift Q) xs)@((Throw,Normal s')#ys)"
                    using `P0 = P \<and> P1 = Q \<and> Normal s = Normal sa \<and> zs = zsa` `zs = map (lift P1) xs @ ((Throw, Normal s')#ys)` 
    by force
    then have a1:"(n,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call" using CptnModNestSeq3.hyps(5) by blast               
     have "(P, Normal sa::('b, 'c) xstate) = (P0, Normal s)"
    using `P0 = P \<and> P1 = Q \<and> Normal s = Normal sa \<and> zs = zsa` by auto  
    then have "(\<exists>xs s'. (n,\<Gamma>, (P, Normal sa) # xs) \<in> cptn_mod_nest_call \<and>
                        (zsa = map (lift Q) xs \<or>              
                         fst (((P,Normal sa) # xs) ! length xs) = Skip \<and>
                             (\<exists>ys. (n,\<Gamma>, (Q, snd (((P, Normal sa) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
                             zsa = map (lift Q) xs @ (Q, snd (((P, Normal sa) # xs) ! length xs)) # ys) \<or>
                        ((fst(((P, Normal sa)#xs)!length xs)=Throw \<and> 
                          snd(last ((P, Normal sa)#xs)) = Normal s' \<and>
                          (\<exists>ys. (n,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call \<and>
                          zsa=(map (lift Q) xs)@((Throw,Normal s')#ys))))))"
     using P0cptn zsa a1 last lastnormal 
       by blast 
   }  
   thus ?thesis by auto qed  
next 
  case (CptnModNestEnv  \<Gamma> P s t n zs) 
  then have step:"(n,\<Gamma>, (P, t) # zs) \<in> cptn_mod_nest_call" by auto
  have step_e: "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow>\<^sub>e (P, t)" using CptnModNestEnv by auto  
  show ?case     
    proof (cases P)
      case (Seq P1 P2) 
      then have eq_P:"(P, t) # zs = (LanguageCon.com.Seq P1 P2, t) # zs" by auto      
      then  obtain xs t' t'' where 
         p1:"(n,\<Gamma>, (P1, t) # xs) \<in> cptn_mod_nest_call" and p2:"
     (zs = map (lift P2) xs \<or>
      fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Skip \<and>      
      (\<exists>ys. (n,\<Gamma>, (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
            zs =
            map (lift P2) xs @
            (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<or>
      fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Throw \<and>
      snd (last ((P1, t) # xs)) = Normal t' \<and>
      t = Normal t'' \<and> (\<exists>ys. (n,\<Gamma>,(Throw,Normal t')#ys) \<in> cptn_mod_nest_call \<and> 
      zs =
      map (lift P2) xs @
      ((LanguageCon.com.Throw, Normal t')#ys))) " 
        using CptnModNestEnv(3) by auto
      have all_step:"(n,\<Gamma>, (P1, s)#((P1, t) # xs)) \<in> cptn_mod_nest_call" 
        using p1 Env Env_n cptn_mod_nest_call.CptnModNestEnv env_normal_s step_e
      proof -
        have "SmallStepCon.redex P = SmallStepCon.redex P1"
          by (metis SmallStepCon.redex.simps(4) local.Seq)
        then show ?thesis
          by (metis (no_types) Env Env_n cptn_mod_nest_call.CptnModNestEnv env_normal_s p1 step_e)
      qed             
      show ?thesis using p2 
      proof  
        assume "zs = map (lift P2) xs"
        have "(P, t) # zs = map (lift P2) ((P1, t) # xs)"
          by (simp add: `zs = map (lift P2) xs` lift_def local.Seq)
        thus ?thesis using all_step eq_P by fastforce
      next 
        assume 
         "fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Skip \<and>      
         (\<exists>ys. (n,\<Gamma>, (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
            zs = map (lift P2) xs @ (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<or>
          fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Throw \<and>
           snd (last ((P1, t) # xs)) = Normal t' \<and>
           t = Normal t'' \<and> (\<exists>ys. (n,\<Gamma>,(Throw,Normal t')#ys) \<in> cptn_mod_nest_call \<and> 
           zs = map (lift P2) xs @ ((LanguageCon.com.Throw, Normal t')#ys))"
         then show ?thesis 
         proof
           assume 
            a1:"fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Skip \<and>      
               (\<exists>ys. (n,\<Gamma>, (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
               zs = map (lift P2) xs @ (P2, snd (((P1, t) # xs) ! length xs)) # ys)"
               from a1 obtain ys where 
                   p2_exec:"(n,\<Gamma>, (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
                       zs = map (lift P2) xs @
                       (P2, snd (((P1, t) # xs) ! length xs)) # ys" 
                by auto 
               have f1:"fst (((P1, s)#(P1, t) # xs) ! length ((P1, t)#xs)) = LanguageCon.com.Skip"
                 using a1 by fastforce             
               then have p2_long_exec: 
                 "(n,\<Gamma>, (P2, snd (((P1, s)#(P1, t) # xs) ! length ((P1, t)#xs))) # ys) \<in> cptn_mod_nest_call \<and>
                  (P, t)#zs = map (lift P2) ((P1, t) # xs) @
                       (P2, snd (((P1, s)#(P1, t) # xs) ! length ((P1, t)#xs))) # ys" 
             using p2_exec by (simp add: lift_def local.Seq)     
             thus ?thesis using a1 f1 all_step eq_P by blast            
           next
           assume 
            a1:"fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Throw \<and>
            snd (last ((P1, t) # xs)) = Normal t' \<and> t = Normal t'' \<and> 
          (\<exists>ys. (n,\<Gamma>,(Throw,Normal t')#ys) \<in> cptn_mod_nest_call \<and> 
           zs = map (lift P2) xs @ ((LanguageCon.com.Throw, Normal t')#ys))"             
             then have last_throw:
               "fst (((P1, s)#(P1, t) # xs) ! length ((P1, t) #xs)) = LanguageCon.com.Throw" 
               by fastforce
             from a1 have last_normal: "snd (last ((P1, s)#(P1, t) # xs)) = Normal t'"
               by fastforce
             have seq_lift:
               "(LanguageCon.com.Seq P1 P2, t) # map (lift P2) xs = map (lift P2) ((P1, t) # xs)"
                by (simp add: a1 lift_def)             
            thus  ?thesis using a1 last_throw last_normal all_step eq_P         
              by (clarify, metis (no_types, lifting) append_Cons env_normal_s'_normal_s  step_e)                 
          qed
      qed
    qed (auto) 
qed (force)+

lemma map_lift_eq_xs_xs':"map (lift a) xs = map (lift a) xs' \<Longrightarrow> xs=xs'" 
proof (induct xs arbitrary: xs')
  case Nil thus ?case by auto
next
  case (Cons x xsa)
  then have a0:"(lift a) x # map (lift a) xsa = map (lift a) (x # xsa)"
    by fastforce 
  also obtain x' xsa' where xs':"xs' = x'#xsa'" 
    using Cons by auto
  ultimately have a1:"map (lift a) (x # xsa) =map (lift a) (x' # xsa')"
    using Cons by auto
  then have xs:"xsa=xsa'" using a0 a1 Cons by fastforce
  then have "(lift a) x' = (lift a) x" using a0 a1  by auto
  then have "x' = x" unfolding lift_def
    by (metis (no_types, lifting) LanguageCon.com.inject(3) 
               case_prod_beta old.prod.inject prod.collapse)   
  thus ?case using xs xs' by auto
qed

lemma map_lift_catch_eq_xs_xs':"map (lift_catch a) xs = map (lift_catch a) xs' \<Longrightarrow> xs=xs'" 
proof (induct xs arbitrary: xs')
  case Nil thus ?case by auto
next
  case (Cons x xsa)
  then have a0:"(lift_catch a) x # map (lift_catch a) xsa = map (lift_catch a) (x # xsa)"
    by auto 
  also obtain x' xsa' where xs':"xs' = x'#xsa'" 
    using Cons by auto
  ultimately have a1:"map (lift_catch a) (x # xsa) =map (lift_catch a) (x' # xsa')"
    using Cons by auto  
  then have xs:"xsa=xsa'" using a0 a1 Cons by fastforce  
  then have "(lift_catch a) x' = (lift_catch a) x" using a0 a1  by auto
  then have "x' = x" unfolding lift_catch_def
    by (metis (no_types, lifting) LanguageCon.com.inject(9) 
               case_prod_beta old.prod.inject prod.collapse)   
  thus ?case using xs xs' by auto
qed

lemma map_lift_all_seq:
 assumes a0:"zs=map (lift a) xs" and
         a1:"i<length zs"
 shows "\<exists>b. fst (zs!i) = Seq b a"
using a0 a1
proof (induct zs arbitrary: xs i)
  case Nil thus ?case by auto
next
  case (Cons z1 zsa) thus ?case unfolding lift_def
  proof -
    assume a1: "z1 # zsa = map (\<lambda>b. case b of (P, s) \<Rightarrow> (LanguageCon.com.Seq P a, s)) xs"
    have "\<forall>p c. \<exists>x. \<forall>pa ca xa. 
            (pa \<noteq> (ca::('a, 'b, 'c, 'd) LanguageCon.com, xa::('a, 'c) xstate) \<or> ca = fst pa) \<and> 
            ((c::('a, 'b, 'c, 'd) LanguageCon.com) \<noteq> fst p \<or> (c, x::('a, 'c) xstate) = p)"
      by fastforce
    then obtain xx :: "('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> ('a, 'b, 'c, 'd) LanguageCon.com \<Rightarrow> ('a, 'c) xstate" where
      "\<And>p c x ca pa. (p \<noteq> (c::('a, 'b, 'c, 'd) LanguageCon.com, x::('a, 'c) xstate) \<or> c = fst p) \<and> (ca \<noteq> fst pa \<or> (ca, xx pa ca) = pa)"
      by (metis (full_types))  
    then show ?thesis
      using a1 \<open>i < length (z1 # zsa)\<close>
      by (simp add: Cons.hyps Cons.prems(1) case_prod_beta')
  qed
qed

lemma map_lift_catch_all_catch:
 assumes a0:"zs=map (lift_catch a) xs" and
         a1:"i<length zs"
 shows "\<exists>b. fst (zs!i) = Catch b a"
using a0 a1
proof (induct zs arbitrary: xs i)
  case Nil thus ?case by auto
next
  case (Cons z1 zsa) thus ?case unfolding lift_catch_def
  proof -
    assume a1: "z1 # zsa = map (\<lambda>b. case b of (P, s) \<Rightarrow> (LanguageCon.com.Catch P a, s)) xs"
    have "\<forall>p c. \<exists>x. \<forall>pa ca xa. 
            (pa \<noteq> (ca::('a, 'b, 'c, 'd) LanguageCon.com, xa::('a, 'c) xstate) \<or> ca = fst pa) \<and> 
            ((c::('a, 'b, 'c, 'd) LanguageCon.com) \<noteq> fst p \<or> (c, x::('a, 'c) xstate) = p)"
      by fastforce
    then obtain xx :: "('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> ('a, 'b, 'c, 'd) LanguageCon.com \<Rightarrow> ('a, 'c) xstate" where
      "\<And>p c x ca pa. (p \<noteq> (c::('a, 'b, 'c, 'd) LanguageCon.com, x::('a, 'c) xstate) \<or> c = fst p) \<and> (ca \<noteq> fst pa \<or> (ca, xx pa ca) = pa)"
      by (metis (full_types))  
    then show ?thesis
      using a1 \<open>i < length (z1 # zsa)\<close>
      by (simp add: Cons.hyps Cons.prems(1) case_prod_beta')
  qed
qed

lemma map_lift_some_eq_pos:
 assumes a0:"map (lift P) xs @ (P1, s1)#ys = 
             map (lift P) xs'@ (P2, s2)#ys'" and
         a1:"\<forall>p0. P1\<noteq>Seq p0 P" and
         a2:"\<forall>p0. P2\<noteq>Seq p0 P" 
 shows "length xs = length xs'"
proof -
  {assume ass:"length xs \<noteq> length xs'"
   { assume ass:"length xs < length xs'"
     then have False using a0  map_lift_all_seq a1 a2
     by (metis (no_types, lifting) fst_conv length_map nth_append nth_append_length)
   }note l=this
   { assume ass:"length xs > length xs'"
     then have False using a0  map_lift_all_seq a1 a2
     by (metis (no_types, lifting) fst_conv length_map nth_append nth_append_length)
   }  then have False using l ass by fastforce
  }
  thus ?thesis by auto
qed

lemma map_lift_some_eq:
 assumes a0:"map (lift P) xs @ (P1, s1)#ys = 
             map (lift P) xs'@ (P2, s2)#ys'" and
        a1:"\<forall>p0. P1\<noteq>Seq p0 P" and
        a2:"\<forall>p0. P2\<noteq>Seq p0 P" 
 shows "xs' = xs \<and> ys = ys'"
proof -
  have "length xs = length xs'" using a0 map_lift_some_eq_pos a1 a2 by blast
  also have "xs' = xs" using a0 assms calculation map_lift_eq_xs_xs' by fastforce
  ultimately show ?thesis using a0 by fastforce
qed

lemma map_lift_catch_some_eq_pos:
 assumes a0:"map (lift_catch P) xs @ (P1, s1)#ys = 
             map (lift_catch P) xs'@ (P2, s2)#ys'" and
         a1:"\<forall>p0. P1\<noteq>Catch p0 P" and
         a2:"\<forall>p0. P2\<noteq>Catch p0 P" 
 shows "length xs = length xs'"
proof -
  {assume ass:"length xs \<noteq> length xs'"
   { assume ass:"length xs < length xs'"
     then have False using a0  map_lift_catch_all_catch a1 a2
     by (metis (no_types, lifting) fst_conv length_map nth_append nth_append_length)
   }note l=this
   { assume ass:"length xs > length xs'"
     then have False using a0  map_lift_catch_all_catch a1 a2
     by (metis (no_types, lifting) fst_conv length_map nth_append nth_append_length)
   }  then have False using l ass by fastforce
  }
  thus ?thesis by auto
qed

lemma map_lift_catch_some_eq:
 assumes a0:"map (lift_catch P) xs @ (P1, s1)#ys = 
             map (lift_catch P) xs'@ (P2, s2)#ys'" and
        a1:"\<forall>p0. P1\<noteq>Catch p0 P" and
        a2:"\<forall>p0. P2\<noteq>Catch p0 P" 
 shows "xs' = xs \<and> ys = ys'"
proof -
  have "length xs = length xs'" using a0 map_lift_catch_some_eq_pos a1 a2 by blast
  also have "xs' = xs" using a0 assms calculation map_lift_catch_eq_xs_xs' by fastforce
  ultimately show ?thesis using a0 by fastforce
qed


lemma Seq_P_Not_finish:
 assumes
   a0:"zs = map (lift Q) xs" and
   a1:"(m, \<Gamma>,(LanguageCon.com.Seq P Q, s) # zs) \<in> cptn_mod_nest_call" and
   a2:"seq_cond_nest zs Q xs' P s s'' s' \<Gamma> m" 
shows "xs=xs'"
using a2 unfolding seq_cond_nest_def 
proof
  assume "zs= map (lift Q) xs'"
  then have  "map (lift Q) xs' = 
              map (lift Q) xs" using a0 by auto 
  thus ?thesis using map_lift_eq_xs_xs' by fastforce
next
  assume 
    ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
         (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, s) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys) \<or>
         fst (((P, s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, s) # xs')) = Normal s' \<and>
         s = Normal s'' \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift Q) xs' @ (LanguageCon.com.Throw, Normal s') # ys)"
   {assume 
     ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
        (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, s) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys)"
      then obtain ys where 
         zs:"zs = map (lift Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys" 
             by auto 
      then have zs_while:"fst (zs!(length (map (lift Q) xs'))) =
                   Q"  by (metis fstI nth_append_length) 
      have "length zs = length (map (lift Q) xs' @
         (Q, snd (((P, s) # xs') ! length xs')) # ys)" 
          using zs by auto
      then have "(length (map (lift Q) xs')) < 
                  length zs" by auto       
      then have ?thesis using a0 zs_while map_lift_all_seq
         using seq_and_if_not_eq(4) by fastforce     
   }note l = this
   {assume ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, s) # xs')) = Normal s' \<and>
         s = Normal s'' \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift Q) xs' @ (LanguageCon.com.Throw, Normal s') # ys)"
      then obtain ys where 
            zs:"zs = map (lift Q) xs' @ 
                 (LanguageCon.com.Throw, Normal s') # ys" by auto
      then have zs_while:
          "fst (zs!(length (map (lift Q) xs'))) = Throw"  by (metis fstI nth_append_length) 
       have "length zs = length (map (lift Q) xs' @(LanguageCon.com.Throw, Normal s') # ys)" 
           using zs by auto
       then have "(length (map (lift Q) xs')) < 
                  length zs" by auto       
       then have ?thesis using a0 zs_while map_lift_all_seq
         using seq_and_if_not_eq(4) by fastforce
   } thus ?thesis using l ass by auto
qed

lemma Seq_P_Ends_Normal:
 assumes
   a0:"zs = map (lift Q) xs @ (Q, snd (last ((P, s) # xs))) # ys" and
   a0':"fst (last ((P, s) # xs)) = Skip" and
   a1:"(m, \<Gamma>,(LanguageCon.com.Seq P Q, s) # zs) \<in> cptn_mod_nest_call" and
   a2:"seq_cond_nest zs Q xs' P s s'' s' \<Gamma> m" 
shows "xs=xs' \<and> (m,\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod_nest_call"
using a2 unfolding seq_cond_nest_def 
proof
  assume ass:"zs= map (lift Q) xs'"
  then have  "map (lift Q) xs' = 
              map (lift Q) xs @ (Q, snd (last ((P, s) # xs))) # ys" using a0 by auto 
  then have zs_while:"fst (zs!(length (map (lift Q) xs))) = Q"  
    by (metis a0 fstI nth_append_length) 
  also have "length zs = 
             length (map (lift Q) xs @ (Q, snd (last ((P, s) # xs))) # ys)" 
    using a0 by auto
  then have "(length (map (lift Q) xs)) < length zs" by auto       
  then show ?thesis using ass zs_while map_lift_all_seq
           using seq_and_if_not_eq(4)
  by metis   
next
  assume 
    ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
         (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, s) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys) \<or>
         fst (((P, s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, s) # xs')) = Normal s' \<and>
         s = Normal s'' \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift Q) xs' @ (LanguageCon.com.Throw, Normal s') # ys)"
   {assume 
     ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
        (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, s) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys)"
      then obtain ys' where 
         zs:"zs = map (lift Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys' \<and>
             (m, \<Gamma>, (Q, snd (((P, s) # xs') ! length xs')) # ys') \<in> cptn_mod_nest_call" 
             by auto 
      then have ?thesis
        using  map_lift_some_eq[of Q xs Q _ ys xs' Q _ ys'] 
               zs  a0 seq_and_if_not_eq(4)[of Q] 
        by auto               
   }note l = this
   {assume ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, s) # xs')) = Normal s' \<and>
         s = Normal s'' \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift Q) xs' @ (LanguageCon.com.Throw, Normal s') # ys)"
      then obtain ys' where 
         zs:"zs = map (lift Q) xs' @ (LanguageCon.com.Throw, Normal s') # ys' \<and>
             (m, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys') \<in> cptn_mod_nest_call" 
         by auto
      then have zs_while:
          "fst (zs!(length (map (lift Q) xs'))) = Throw"  by (metis fstI nth_append_length)       
      have False
        by (metis (no_types) LanguageCon.com.distinct(17) 
              LanguageCon.com.distinct(71) 
              a0 a0' ass last_length
              map_lift_some_eq seq_and_if_not_eq(4) zs)
      then have ?thesis
        by metis
   } thus ?thesis using l ass by auto
qed

lemma Seq_P_Ends_Abort:
 assumes
   a0:"zs = map (lift Q) xs @ (Throw, Normal s') # ys" and
   a0':"fst (last ((P, Normal s) # xs)) = Throw" and
   a0'':"snd(last ((P, Normal s) # xs)) = Normal s'" and
   a1:"(m, \<Gamma>,(LanguageCon.com.Seq P Q, Normal s) # zs) \<in> cptn_mod_nest_call" and
   a2:"seq_cond_nest zs Q xs' P (Normal s) ns'' ns' \<Gamma> m" 
shows "xs=xs' \<and> (m,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call"
using a2 unfolding seq_cond_nest_def 
proof
  assume ass:"zs= map (lift Q) xs'"
  then have  "map (lift Q) xs' = 
              map (lift Q) xs @ (Throw, Normal s') # ys" using a0 by auto 
  then have zs_while:"fst (zs!(length (map (lift Q) xs))) = Throw"  
    by (metis a0  fstI nth_append_length) 
  also have "length zs = 
             length (map (lift Q) xs @ (Throw, Normal s') # ys)" 
    using a0 by auto
  then have "(length (map (lift Q) xs)) < length zs" by auto       
  then show ?thesis using ass zs_while map_lift_all_seq    
    by (metis (no_types) LanguageCon.com.simps(82))    
next
  assume 
    ass:"fst (((P, Normal s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
         (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, Normal s) # xs') ! length xs')) # ys)
          \<in> cptn_mod_nest_call \<and>
         zs = map (lift Q) xs' @
              (Q, snd (((P, Normal s) # xs') ! length xs')) # ys) \<or>
         fst (((P, Normal s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, Normal s) # xs')) = Normal ns' \<and>
         Normal s = Normal ns'' \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Throw, Normal ns') # ys) \<in> cptn_mod_nest_call \<and>
            zs = map (lift Q) xs' @ (LanguageCon.com.Throw, Normal ns') # ys)"
   {assume 
     ass:"fst (((P, Normal s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
         (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, Normal s) # xs') ! length xs')) # ys)
          \<in> cptn_mod_nest_call \<and>
         zs = map (lift Q) xs' @
              (Q, snd (((P, Normal s) # xs') ! length xs')) # ys)"
      then obtain ys' where 
         zs:"(m, \<Gamma>, (Q, snd (((P, Normal s) # xs') ! length xs')) # ys')
               \<in> cptn_mod_nest_call \<and>
            zs = map (lift Q) xs' @ 
              (Q, snd (((P, Normal s) # xs') ! length xs')) # ys'" 
             by auto 
      then have ?thesis
        using a0 seq_and_if_not_eq(4)[of Q]
         by (metis LanguageCon.com.distinct(17) LanguageCon.com.distinct(71) 
             a0' ass last_length map_lift_some_eq)                        
   }note l = this
   {assume ass:"fst (((P, Normal s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, Normal s) # xs')) = Normal ns' \<and>
         Normal s = Normal ns'' \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Throw, Normal ns') # ys) \<in> cptn_mod_nest_call \<and>
            zs = map (lift Q) xs' @ (LanguageCon.com.Throw, Normal ns') # ys)"
      then obtain ys' where 
         zs:"(m, \<Gamma>, (LanguageCon.com.Throw, Normal ns') # ys') \<in> cptn_mod_nest_call \<and>
            zs = map (lift Q) xs' @ (LanguageCon.com.Throw, Normal ns') # ys'" 
         by auto
      then have zs_while:
          "fst (zs!(length (map (lift Q) xs'))) = Throw"  
        by (metis fstI nth_append_length)             
      then have ?thesis using a0 ass map_lift_some_eq by blast        
   } thus ?thesis using l ass by auto
qed

lemma Catch_P_Not_finish:
 assumes
   a0:"zs = map (lift_catch Q) xs" and   
   a1:"catch_cond_nest zs Q xs' P s s'' s' \<Gamma> m" 
shows "xs=xs'"
using a1 unfolding catch_cond_nest_def 
proof
  assume "zs= map (lift_catch Q) xs'"
  then have  "map (lift_catch Q) xs' = 
              map (lift_catch Q) xs" using a0 by auto 
  thus ?thesis using map_lift_catch_eq_xs_xs' by fastforce
next
  assume 
    ass:"
         fst (((P, s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, s) # xs')) = Normal s' \<and>
         s = Normal s'' \<and>
         (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, s) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys) \<or>
         fst (((P, s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys)"
   {assume 
     ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys)"
      then obtain ys where 
         zs:"(m, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys) \<in> cptn_mod_nest_call \<and>
            zs = map (lift_catch Q) xs' @ (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys" 
             by auto 
      then have zs_while:"fst (zs!(length (map (lift_catch Q) xs'))) = Skip "  
        by (metis fstI nth_append_length) 
      have "length zs = length (map (lift Q) xs' @
         (Q, snd (((P, s) # xs') ! length xs')) # ys)" 
          using zs by auto
      then have "(length (map (lift Q) xs')) < 
                  length zs" by auto       
      then have ?thesis using a0 zs_while map_lift_catch_all_catch
         using seq_and_if_not_eq(12) by fastforce     
   }note l = this
   {assume ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, s) # xs')) = Normal s' \<and>
         s = Normal s'' \<and>
         (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, s) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys)"
      then obtain ys where 
            zs:"zs = map (lift_catch Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys" by auto
      then have zs_while:
        "fst (zs!(length (map (lift Q) xs'))) = Q"
         by (metis (no_types) eq_fst_iff length_map nth_append_length zs) 
       have "length zs = length (map (lift Q) xs' @(LanguageCon.com.Throw, Normal s') # ys)" 
           using zs by auto
       then have "(length (map (lift Q) xs')) < 
                  length zs" by auto       
       then have ?thesis using a0 zs_while map_lift_catch_all_catch
         by fastforce
   } thus ?thesis using l ass by auto
qed

lemma Catch_P_Ends_Normal:
 assumes
   a0:"zs = map (lift_catch Q) xs @ (Q, snd (last ((P, Normal s) # xs))) # ys" and
   a0':"fst (last ((P, Normal s) # xs)) = Throw" and
   a0'':"snd (last ((P, Normal s) # xs)) = Normal s'" and
   a1:"catch_cond_nest zs Q xs' P (Normal s) ns'' ns' \<Gamma> m" 
shows "xs=xs' \<and> (m,\<Gamma>,(Q, snd(((P, Normal s)#xs)!length xs))#ys) \<in> cptn_mod_nest_call"
using a1 unfolding catch_cond_nest_def 
proof
  assume ass:"zs= map (lift_catch Q) xs'"
  then have  "map (lift_catch Q) xs' = 
              map (lift_catch Q) xs @ (Q, snd (last ((P, Normal s) # xs))) # ys" using a0 by auto 
  then have zs_while:"fst (zs!(length (map (lift_catch Q) xs))) = Q"
    by (metis a0 fstI nth_append_length)      
  also have "length zs = 
             length (map (lift_catch Q) xs @ (Q, snd (last ((P, Normal s) # xs))) # ys)" 
    using a0 by auto
  then have "(length (map (lift_catch Q) xs)) < length zs" by auto       
  then show ?thesis using ass zs_while map_lift_catch_all_catch
           using seq_and_if_not_eq(12)
  by metis
next
  assume 
    ass:"fst (((P, Normal s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, Normal s) # xs')) = Normal ns' \<and>
         Normal s = Normal ns'' \<and>
         (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, Normal s) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (Q, snd (((P, Normal s) # xs') ! length xs')) # ys) \<or>
         fst (((P, Normal s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P, Normal s) # xs'))) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (LanguageCon.com.Skip, snd (last ((P, Normal s) # xs'))) # ys)"
   {assume 
     ass:"fst (((P, Normal s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P, Normal s) # xs'))) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (LanguageCon.com.Skip, snd (last ((P, Normal s) # xs'))) # ys)"
      then obtain ys' where 
         zs:"(m, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P, Normal s) # xs'))) # ys') \<in> cptn_mod_nest_call \<and>
             zs = map (lift_catch Q) xs' @ (LanguageCon.com.Skip, snd (last ((P, Normal s) # xs'))) # ys'" 
             by auto 
      then have ?thesis
        using  map_lift_catch_some_eq[of Q xs Q _ ys xs' Skip _ ys'] 
               zs  a0 seq_and_if_not_eq(12)[of Q]
        by (metis LanguageCon.com.distinct(17) LanguageCon.com.distinct(19) a0' ass last_length)                        
   }note l = this
   {assume ass:"fst (((P, Normal s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
                snd (last ((P, Normal s) # xs')) = Normal ns' \<and>
                Normal s = Normal ns'' \<and>
                (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, Normal s) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                zs = map (lift_catch Q) xs' @ (Q, snd (((P, Normal s) # xs') ! length xs')) # ys)"
      then obtain ys' where 
         zs:"(m, \<Gamma>, (Q, snd (((P, Normal s) # xs') ! length xs')) # ys') \<in> cptn_mod_nest_call \<and>
                zs = map (lift_catch Q) xs' @ (Q, snd (((P, Normal s) # xs') ! length xs')) # ys'" 
         by auto
      then have zs_while:
          "fst (zs!(length (map (lift_catch Q) xs'))) = Q"  by (metis fstI nth_append_length)       

      then have ?thesis 
        using LanguageCon.com.distinct(17) LanguageCon.com.distinct(71) 
            a0 a0' ass last_length map_lift_catch_some_eq[of Q xs Q _ ys xs' Q _ ys']  
            seq_and_if_not_eq(12) zs
        by blast        
   } thus ?thesis using l ass by auto
qed
 
lemma Catch_P_Ends_Skip:
 assumes
   a0:"zs = map (lift_catch Q) xs @ (Skip, snd (last ((P, s) # xs))) # ys" and
   a0':"fst (last ((P,s) # xs)) = Skip" and
   a1:"catch_cond_nest zs Q xs' P s ns'' ns' \<Gamma> m" 
shows "xs=xs' \<and> (m,\<Gamma>,(Skip,snd(last ((P,s) # xs)))#ys) \<in> cptn_mod_nest_call"
using a1 unfolding catch_cond_nest_def 
proof
  assume ass:"zs= map (lift_catch Q) xs'"
  then have  "map (lift_catch Q) xs' = 
              map (lift_catch Q) xs @ (Skip, snd (last ((P, s) # xs))) # ys" using a0 by auto 
  then have zs_while:"fst (zs!(length (map (lift_catch Q) xs))) = Skip"  
    by (metis a0  fstI nth_append_length) 
  also have "length zs = 
             length (map (lift_catch Q) xs @ (Skip, snd (last ((P, s) # xs))) # ys)" 
    using a0 by auto
  then have "(length (map (lift_catch Q) xs)) < length zs" by auto       
  then show ?thesis using ass zs_while map_lift_catch_all_catch
    by (metis LanguageCon.com.distinct(19))    
next
  assume 
    ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, s) # xs')) = Normal ns' \<and>
         s = Normal ns'' \<and>
         (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, s) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys) \<or>
         fst (((P, s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys)"
   {assume 
     ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys)"
      then obtain ys' where 
         zs:"(m, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys') \<in> cptn_mod_nest_call \<and>
             zs = map (lift_catch Q) xs' @ (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys'" 
             by auto 
      then have ?thesis
        using a0 seq_and_if_not_eq(12)[of Q] a0' ass last_length map_lift_catch_some_eq
        using LanguageCon.com.distinct(19) by blast                
   }note l = this
   {assume ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, s) # xs')) = Normal ns' \<and>
         s = Normal ns'' \<and>
         (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, s) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys)"
      then obtain ys' where 
         zs:"(m, \<Gamma>, (Q, snd (((P, s) # xs') ! length xs')) # ys') \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys'" 
         by auto
      then have zs_while:
          "fst (zs!(length (map (lift_catch Q) xs'))) = Q"  
        by (metis fstI nth_append_length)             
      then have ?thesis 
        using a0 seq_and_if_not_eq(12)[of Q] a0' ass last_length map_lift_catch_some_eq
        by (metis LanguageCon.com.distinct(17) LanguageCon.com.distinct(19))               
   } thus ?thesis using l ass by auto
qed


lemma not_func_redex_cptn_mod_nest_n': 
assumes a0:"\<Gamma>\<turnstile>\<^sub>c (P,s) \<rightarrow> (Q, t)" and
        a1:"(n,\<Gamma>,(Q,t)#xs) \<in>  cptn_mod_nest_call" and 
        a2:"(\<forall>fn. redex P \<noteq> Call fn) \<or> 
            (redex P = Call fn \<and> \<Gamma> fn = None) \<or> 
            (redex P = Call fn \<and> (\<forall>sa. s\<noteq>Normal sa))"
shows "(n,\<Gamma>,(P,s)#(Q,t)#xs) \<in>  cptn_mod_nest_call"
using a0 a1 a2
proof (induct arbitrary: xs) 
  case (Basicc f s)   
  thus ?case by (simp add: Basicc cptn_mod_nest_call.CptnModNestSkip stepc.Basicc)
next
  case (Specc s t r)
  thus ?case by (simp add: Specc cptn_mod_nest_call.CptnModNestSkip stepc.Specc)
next
  case (SpecStuckc s r)
  thus ?case by (simp add: SpecStuckc cptn_mod_nest_call.CptnModNestSkip stepc.SpecStuckc)
next
  case (Guardc s g f c) 
    thus ?case by (simp add: cptn_mod_nest_call.CptnModNestGuard) 
next

  case (GuardFaultc s g f c)
  thus ?case by (simp add: GuardFaultc cptn_mod_nest_call.CptnModNestSkip stepc.GuardFaultc)
next
case (Seqc c1 s c1' s' c2)
  have step: "\<Gamma>\<turnstile>\<^sub>c (c1, s) \<rightarrow> (c1', s')" by (simp add: Seqc.hyps(1))
  then have nsc1: "c1\<noteq>Skip" using stepc_elim_cases(1) by blast 
  have assum: "(n, \<Gamma>, (Seq c1' c2, s') # xs) \<in> cptn_mod_nest_call" using Seqc.prems by blast
  have divseq:"(\<forall>s P Q zs. (Seq c1' c2, s') # xs=(Seq P Q, s)#zs \<longrightarrow>
                (\<exists>xs sv' sv''. ((n,\<Gamma>,(P, s)#xs) \<in> cptn_mod_nest_call  \<and> 
                           (zs=(map (lift Q) xs) \<or>
                           ((fst(((P, s)#xs)!length xs)=Skip \<and> 
                             (\<exists>ys. (n,\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod_nest_call \<and> 
                              zs=(map (lift (Q)) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
                           ((fst(((P, s)#xs)!length xs)=Throw \<and> 
                               snd(last ((P, s)#xs)) = Normal sv' \<and>  s'=Normal sv''\<and>
                             (\<exists>ys.  (n,\<Gamma>,(Throw,Normal sv')#ys) \<in> cptn_mod_nest_call \<and>
                              zs=(map (lift Q) xs)@((Throw,Normal sv')#ys))
                               ))))
                            
                 ))"  using div_seq_nest [OF assum] unfolding seq_cond_nest_def by auto
   {fix sa P Q zsa
       assume ass:"(Seq c1' c2, s') # xs = (Seq P Q, sa) # zsa"
       then have eqs:"c1' = P \<and> c2 = Q \<and> s' = sa \<and> xs = zsa" by auto
       then have "(\<exists>xs sv' sv''. (n,\<Gamma>, (P, sa) # xs) \<in> cptn_mod_nest_call \<and>
                        (zsa = map (lift Q) xs \<or>              
                         fst (((P, sa) # xs) ! length xs) = Skip \<and>
                             (\<exists>ys. (n,\<Gamma>, (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
                             zsa = map (lift Q) xs @ (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<or>
                        ((fst(((P, sa)#xs)!length xs)=Throw \<and> 
                          snd(last ((P, sa)#xs)) = Normal sv' \<and>  s'=Normal sv''\<and>
                          (\<exists>ys.  (n,\<Gamma>,(Throw,Normal sv')#ys) \<in> cptn_mod_nest_call \<and>
                              zsa=(map (lift Q) xs)@((Throw,Normal sv')#ys))))))" 
             using ass divseq by blast
    } note conc=this [of c1' c2 s' xs]    
     then obtain xs' sa' sa''
       where  split:"(n,\<Gamma>, (c1', s') # xs') \<in> cptn_mod_nest_call \<and>
                     (xs = map (lift c2) xs' \<or>                   
                     fst (((c1', s') # xs') ! length xs') = Skip \<and>
                        (\<exists>ys. (n,\<Gamma>, (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                         xs = map (lift c2) xs' @ (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<or>
                     ((fst(((c1', s')#xs')!length xs')=Throw \<and> 
                         snd(last ((c1', s')#xs')) = Normal sa' \<and> s'=Normal sa''\<and>
                         (\<exists>ys.  (n,\<Gamma>,(Throw,Normal sa')#ys) \<in> cptn_mod_nest_call \<and>
                              xs=(map (lift c2) xs')@((Throw,Normal sa')#ys))
                         )))"  by blast
  then have "(xs = map (lift c2) xs' \<or>                   
                   fst (((c1', s') # xs') ! length xs') = Skip \<and>
                      (\<exists>ys. (n,\<Gamma>, (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                       xs = map (lift c2) xs' @ (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<or>
                   ((fst(((c1', s')#xs')!length xs')=Throw \<and> 
                       snd(last ((c1', s')#xs')) = Normal sa' \<and> s'=Normal sa''\<and>
                       (\<exists>ys.  (n,\<Gamma>,(Throw,Normal sa')#ys) \<in> cptn_mod_nest_call \<and>
                            xs=(map (lift c2) xs')@((Throw,Normal sa')#ys)))))" 
    by auto
  thus ?case 
  proof{           
       assume c1'nonf:"xs = map (lift c2) xs'"
       then have c1'cptn:"(n,\<Gamma>, (c1', s') # xs') \<in> cptn_mod_nest_call" using split by blast
       then have induct_step: "(n,\<Gamma>, (c1, s) # (c1', s')#xs') \<in> cptn_mod_nest_call"
         using Seqc.hyps(2) Seqc.prems(2) SmallStepCon.redex.simps(4) by auto  
       then have "(Seq c1' c2, s')#xs = map (lift c2) ((c1', s')#xs')"
         using c1'nonf
         by (simp add: lift_def)
       thus ?thesis 
         using c1'nonf c1'cptn induct_step by (auto simp add: CptnModNestSeq1)
    next
      assume "fst (((c1', s') # xs') ! length xs') = Skip \<and>
              (\<exists>ys. (n,\<Gamma>, (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                  xs = map (lift c2) xs' @ (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<or>
             ((fst(((c1', s')#xs')!length xs')=Throw \<and> 
                snd(last ((c1', s')#xs')) = Normal sa' \<and>  s'=Normal sa''\<and>
                (\<exists>ys.  (n,\<Gamma>,(Throw,Normal sa')#ys) \<in> cptn_mod_nest_call \<and>
                              xs=(map (lift c2) xs')@((Throw,Normal sa')#ys))))"  
      thus ?thesis
      proof
       assume assth:"fst (((c1', s') # xs') ! length xs') = Skip \<and>
            (\<exists>ys. (n,\<Gamma>, (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                xs = map (lift c2) xs' @ (c2, snd (((c1', s') # xs') ! length xs')) # ys)"
       then obtain ys 
           where split':"(n,\<Gamma>, (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                xs = map (lift c2) xs' @ (c2, snd (((c1', s') # xs') ! length xs')) # ys"
           by auto    
       then have c1'cptn:"(n,\<Gamma>, (c1', s') # xs') \<in> cptn_mod_nest_call" using split by blast
       then have induct_step: "(n,\<Gamma>, (c1, s) # (c1', s')#xs') \<in> cptn_mod_nest_call"
       using Seqc.hyps(2) Seqc.prems(2) SmallStepCon.redex.simps(4) by auto                
       then have seqmap:"(Seq c1 c2, s)#(Seq c1' c2, s')#xs = map (lift c2) ((c1,s)#(c1', s')#xs') @ (c2, snd (((c1', s') # xs') ! length xs')) # ys"
      using split' by (simp add:  lift_def) 
      then have lastc1:"last ((c1, s) # (c1', s') # xs') = ((c1', s') # xs') ! length xs'"
        by (simp add: last_length) 
      then have lastc1skip:"fst (last ((c1, s) # (c1', s') # xs')) = Skip" 
           using assth by fastforce          
      thus ?thesis 
        using seqmap split' cptn_mod_nest_call.CptnModNestSeq2
              induct_step lastc1 lastc1skip
        by (metis (no_types) Cons_lift_append )               
    next
        assume assm:"((fst(((c1', s')#xs')!length xs')=Throw \<and> 
                snd(last ((c1', s')#xs')) = Normal sa' \<and>  s'=Normal sa''\<and>
                (\<exists>ys.(n,\<Gamma>,(Throw,Normal sa')#ys) \<in> cptn_mod_nest_call \<and>
                 xs=(map (lift c2) xs')@((Throw,Normal sa')#ys))))"
        then have s'eqsa'': "s'=Normal sa''" by auto
        then have snormal: "\<exists>ns. s=Normal ns" by (metis Seqc.hyps(1) step_Abrupt_prop step_Fault_prop step_Stuck_prop xstate.exhaust)
        then have c1'cptn:"(n,\<Gamma>, (c1', s') # xs') \<in> cptn_mod_nest_call" using split by blast        
        then have induct_step: "(n,\<Gamma>, (c1, s) # (c1', s')#xs') \<in> cptn_mod_nest_call"
        using Seqc.hyps(2) Seqc.prems(2) SmallStepCon.redex.simps(4) by auto 
        then obtain ys where seqmap:"(Seq c1' c2, s')#xs = (map (lift c2) ((c1', s')#xs'))@((Throw,Normal sa')#ys)"
        using assm
        proof -
          assume a1: "\<And>ys. (LanguageCon.com.Seq c1' c2, s') # xs = map (lift c2) ((c1', s') # xs') @ (LanguageCon.com.Throw, Normal sa') # ys \<Longrightarrow> thesis"
          have "(LanguageCon.com.Seq c1' c2, Normal sa'') # map (lift c2) xs' = map (lift c2) ((c1', s') # xs')"
            by (simp add: assm lift_def)
          thus ?thesis
            using a1 assm by moura
        qed  
        then have lastc1:"last ((c1, s) # (c1', s') # xs') = ((c1', s') # xs') ! length xs'"
                   by (simp add: last_length) 
        then have lastc1skip:"fst (last ((c1, s) # (c1', s') # xs')) = Throw" 
             using assm by fastforce
        then have "snd (last ((c1, s) # (c1', s') # xs')) = Normal sa'"
             using assm by force        
        thus ?thesis
            using assm c1'cptn induct_step lastc1skip snormal seqmap s'eqsa'' 
            by (auto simp add:cptn_mod_nest_call.CptnModNestSeq3)
   qed
  }qed    
next
  case (SeqSkipc c2 s xs)
  have c2incptn:"(n,\<Gamma>, (c2, s) # xs) \<in> cptn_mod_nest_call" by fact
  then have 1:"(n,\<Gamma>, [(Skip, s)]) \<in> cptn_mod_nest_call"
    by (simp add: cptn_mod_nest_call.CptnModNestOne)
  then have 2:"fst(last ([(Skip, s)])) = Skip" by fastforce
  then have 3:"(n,\<Gamma>,(c2, snd(last [(Skip, s)]))#xs) \<in> cptn_mod_nest_call" 
      using c2incptn by auto  
  then have "(c2,s)#xs=(map (lift c2) [])@(c2, snd(last [(Skip, s)]))#xs" 
       by (auto simp add:lift_def)
  thus ?case using 1 2 3 by (simp add: CptnModNestSeq2)   
next
  case (SeqThrowc c2 s xs)  
  have "(n,\<Gamma>, [(Throw, Normal s)]) \<in> cptn_mod_nest_call" 
    by (simp add: cptn_mod_nest_call.CptnModNestOne) 
  then obtain ys where 
    ys_nil:"ys=[]" and 
    last:"(n, \<Gamma>, (Throw, Normal s)#ys)\<in> cptn_mod_nest_call"
   by auto
  moreover have "fst (last ((Throw, Normal s)#ys)) = Throw" using ys_nil last by auto
  moreover have "snd (last ((Throw, Normal s)#ys)) = Normal s" using ys_nil last by auto
  moreover from ys_nil have "(map (lift c2) ys) = []" by auto  
  ultimately show ?case using SeqThrowc.prems cptn_mod_nest_call.CptnModNestSeq3 by fastforce      

next
  case (CondTruec s b c1 c2)
  thus ?case by (simp add: cptn_mod_nest_call.CptnModNestCondT)
next
  case (CondFalsec s b c1 c2)
  thus ?case by (simp add: cptn_mod_nest_call.CptnModNestCondF)
next
 case (WhileTruec s1 b c)
 have sinb: "s1\<in>b" by fact
 have SeqcWhile: "(n,\<Gamma>, (Seq c (While b c), Normal s1) # xs) \<in> cptn_mod_nest_call" 
   by fact  
 have divseq:"(\<forall>s P Q zs. (Seq c (While b c), Normal s1) # xs=(Seq P Q, s)#zs \<longrightarrow>
                (\<exists>xs s'. ((n,\<Gamma>,(P, s)#xs) \<in> cptn_mod_nest_call  \<and> 
                           (zs=(map (lift Q) xs) \<or>
                           ((fst(((P, s)#xs)!length xs)=Skip \<and> 
                             (\<exists>ys. (n,\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod_nest_call \<and> 
                              zs=(map (lift (Q)) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
                           ((fst(((P, s)#xs)!length xs)=Throw \<and> 
                               snd(last ((P, s)#xs)) = Normal s' \<and>
                              (\<exists>ys.  (n,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call \<and>
                      zs=(map (lift Q) xs)@((Throw,Normal s')#ys))))))                            
                 ))" using div_seq_nest [OF SeqcWhile] by (auto simp add: seq_cond_nest_def)
{fix sa P Q zsa
       assume ass:"(Seq c (While b c), Normal s1) # xs = (Seq P Q, sa) # zsa"
       then have eqs:"c = P \<and> (While b c) = Q \<and> Normal s1 = sa \<and> xs = zsa" by auto
       then have "(\<exists>xs s'. (n,\<Gamma>, (P, sa) # xs) \<in> cptn_mod_nest_call \<and>
                        (zsa = map (lift Q) xs \<or>              
                         fst (((P, sa) # xs) ! length xs) = Skip \<and>
                             (\<exists>ys. (n,\<Gamma>, (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
                             zsa = map (lift Q) xs @ (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<or>
                        ((fst(((P, sa)#xs)!length xs)=Throw \<and> 
                          snd(last ((P, sa)#xs)) = Normal s' \<and>
                          (\<exists>ys.  (n,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call \<and>
                      zsa=(map (lift Q) xs)@((Throw,Normal s')#ys))
                        ))))" 
             using ass divseq by auto
    } note conc=this [of c "While b c" "Normal s1" xs] 
   then obtain xs' s' 
        where  split:"(n,\<Gamma>, (c, Normal s1) # xs') \<in> cptn_mod_nest_call \<and>
     (xs = map (lift (While b c)) xs' \<or>
      fst (((c, Normal s1) # xs') ! length xs') = Skip \<and>
      (\<exists>ys. (n,\<Gamma>, (While b c, snd (((c, Normal s1) # xs') ! length xs')) # ys)
            \<in> cptn_mod_nest_call \<and>
            xs =
            map (lift (While b c)) xs' @
            (While b c, snd (((c, Normal s1) # xs') ! length xs')) # ys) \<or>
      fst (((c, Normal s1) # xs') ! length xs') = Throw \<and>
      snd (last ((c, Normal s1) # xs')) = Normal s' \<and> 
      (\<exists>ys.  (n,\<Gamma>, ((Throw, Normal s')#ys)) \<in> cptn_mod_nest_call \<and>
      xs = map (lift (While b c)) xs' @ ((Throw, Normal s')#ys)))"  by auto
 then have "(xs = map (lift (While b c)) xs' \<or>
            fst (((c, Normal s1) # xs') ! length xs') = Skip \<and>
            (\<exists>ys. (n,\<Gamma>, (While b c, snd (((c, Normal s1) # xs') ! length xs')) # ys)
                  \<in> cptn_mod_nest_call \<and>
                  xs =
                  map (lift (While b c)) xs' @
                  (While b c, snd (((c, Normal s1) # xs') ! length xs')) # ys) \<or>
            fst (((c, Normal s1) # xs') ! length xs') = Throw \<and>
            snd (last ((c, Normal s1) # xs')) = Normal s' \<and>
            (\<exists>ys.  (n,\<Gamma>, ((Throw, Normal s')#ys)) \<in> cptn_mod_nest_call \<and>
          xs = map (lift (While b c)) xs' @ ((Throw, Normal s')#ys)))" ..
 thus ?case
 proof{ 
   assume 1:"xs = map (lift (While b c)) xs'"  
   have 3:"(n, \<Gamma>, (c, Normal s1) # xs') \<in> cptn_mod_nest_call" using split by auto   
   then show ?thesis 
     using "1" cptn_mod_nest_call.CptnModNestWhile1 sinb by fastforce 
 next
   assume "fst (((c, Normal s1) # xs') ! length xs') = Skip \<and>
          (\<exists>ys. (n,\<Gamma>, (While b c, snd (((c, Normal s1) # xs') ! length xs')) # ys)
                \<in> cptn_mod_nest_call \<and>
                xs =
                map (lift (While b c)) xs' @
                (While b c, snd (((c, Normal s1) # xs') ! length xs')) # ys) \<or>
          fst (((c, Normal s1) # xs') ! length xs') = Throw \<and>
          snd (last ((c, Normal s1) # xs')) = Normal s' \<and>
          (\<exists>ys.  (n,\<Gamma>, ((Throw, Normal s')#ys)) \<in> cptn_mod_nest_call \<and>
          xs = map (lift (While b c)) xs' @ ((Throw, Normal s')#ys))"
   thus ?case
   proof
     assume asm:"fst (((c, Normal s1) # xs') ! length xs') = Skip \<and>
             (\<exists>ys. (n,\<Gamma>, (While b c, snd (((c, Normal s1) # xs') ! length xs')) # ys)
             \<in> cptn_mod_nest_call \<and>
             xs =
             map (lift (While b c)) xs' @
             (While b c, snd (((c, Normal s1) # xs') ! length xs')) # ys)"
     then obtain ys 
       where asm':"(n,\<Gamma>, (While b c, snd (last ((c, Normal s1) # xs'))) # ys)
                   \<in> cptn_mod_nest_call 
                   \<and> xs = map (lift (While b c)) xs' @
                       (While b c, snd (last ((c, Normal s1) # xs'))) # ys" 
              by (auto simp add: last_length)
     moreover have 3:"(n,\<Gamma>, (c, Normal s1) # xs') \<in> cptn_mod_nest_call" using split by auto
     moreover from asm have "fst (last ((c, Normal s1) # xs'))  = Skip"
          by (simp add: last_length) 
     ultimately show ?case using sinb by (auto simp add:CptnModNestWhile2)
   next
    assume asm:" fst (((c, Normal s1) # xs') ! length xs') = Throw \<and>
          snd (last ((c, Normal s1) # xs')) = Normal s' \<and>
          (\<exists>ys.  (n,\<Gamma>, ((Throw, Normal s')#ys)) \<in> cptn_mod_nest_call \<and>
          xs = map (lift (While b c)) xs' @ ((Throw, Normal s')#ys))"   
     moreover have 3:"(n,\<Gamma>, (c, Normal s1) # xs') \<in> cptn_mod_nest_call" 
       using split by auto
     moreover from asm have "fst (last ((c, Normal s1) # xs'))  = Throw"
          by (simp add: last_length) 
     ultimately show ?case using sinb by (auto simp add:CptnModNestWhile3)
   qed
 }qed  
next
 case (WhileFalsec s b c)
 thus ?case by (simp add: cptn_mod_nest_call.CptnModNestSkip stepc.WhileFalsec)
next
  case (Awaitc s b c t)
  thus ?case by (simp add: cptn_mod_nest_call.CptnModNestSkip stepc.Awaitc)
next
  case (AwaitAbruptc s b c t t')
  thus ?case by (simp add: cptn_mod_nest_call.CptnModNestThrow stepc.AwaitAbruptc) 
next
  case (Callc p bdy s)
  thus ?case using SmallStepCon.redex.simps(7) by auto  
next
  case (CallUndefinedc p s)
  then have "p = fn" by auto
  thus ?case using CallUndefinedc
  proof -
    have "(LanguageCon.com.Call fn \<inter>\<^sub>g\<^sub>s (LanguageCon.com.Skip::('b, 'a, 'c,'d) LanguageCon.com)) \<noteq> Some LanguageCon.com.Skip"
      by simp
    then show ?thesis
      by (metis (no_types) CallUndefinedc.hyps LanguageCon.com.inject(6) LanguageCon.inter_guards.simps(79) SmallStepCon.redex.simps(7) \<open>(n, \<Gamma>, (LanguageCon.com.Skip, Stuck) # xs) \<in> cptn_mod_nest_call\<close> cptn_mod_nest_call.CptnModNestSkip stepc.CallUndefinedc)
  qed 
next
  case (DynComc c s)
  thus ?case by (simp add: cptn_mod_nest_call.CptnModNestDynCom) 
next
  case (Catchc c1 s c1' s' c2)
   have step: "\<Gamma>\<turnstile>\<^sub>c (c1, s) \<rightarrow> (c1', s')" by (simp add: Catchc.hyps(1))
  then have nsc1: "c1\<noteq>Skip" using stepc_elim_cases(1) by blast 
  have assum: "(n,\<Gamma>, (Catch c1' c2, s') # xs) \<in> cptn_mod_nest_call" 
  using Catchc.prems by blast
  have divcatch:"(\<forall>s P Q zs. (Catch c1' c2, s') # xs=(Catch P Q, s)#zs \<longrightarrow>
  (\<exists>xs s' s''. ((n,\<Gamma>,(P, s)#xs) \<in> cptn_mod_nest_call  \<and> 
             (zs=(map (lift_catch Q) xs) \<or>
             ((fst(((P, s)#xs)!length xs)=Throw \<and>
               snd(last ((P, s)#xs)) = Normal s' \<and>  s=Normal s''\<and>
               (\<exists>ys. (n,\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod_nest_call \<and> 
                zs=(map (lift_catch Q) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
                ((fst(((P, s)#xs)!length xs)=Skip \<and>  
                  (\<exists>ys. (n,\<Gamma>,(Skip,snd(last ((P, s)#xs)))#ys) \<in> cptn_mod_nest_call \<and>                   
                 zs=(map (lift_catch Q) xs)@((Skip,snd(last ((P, s)#xs)))#ys))                
                 ))))
   ))" using div_catch_nest [OF assum] by (auto simp add: catch_cond_nest_def)
   {fix sa P Q zsa
       assume ass:"(Catch c1' c2, s') # xs = (Catch P Q, sa) # zsa"
       then have eqs:"c1' = P \<and> c2 = Q \<and> s' = sa \<and> xs = zsa" by auto
       then have "(\<exists>xs sv' sv''. ((n, \<Gamma>,(P, sa)#xs) \<in> cptn_mod_nest_call  \<and> 
             (zsa=(map (lift_catch Q) xs) \<or>
             ((fst(((P, sa)#xs)!length xs)=Throw \<and>
               snd(last ((P, sa)#xs)) = Normal sv' \<and>  s'=Normal sv''\<and>
               (\<exists>ys. (n,\<Gamma>,(Q, snd(((P, sa)#xs)!length xs))#ys) \<in> cptn_mod_nest_call \<and> 
                zsa=(map (lift_catch Q) xs)@((Q, snd(((P, sa)#xs)!length xs))#ys)))) \<or>
                ((fst(((P, sa)#xs)!length xs)=Skip \<and>                  
                 (\<exists>ys. (n,\<Gamma>,(Skip,snd(last ((P, sa)#xs)))#ys) \<in> cptn_mod_nest_call \<and>                   
                 zsa=(map (lift_catch Q) xs)@((Skip,snd(last ((P, sa)#xs)))#ys))))))
   )"   using ass divcatch by blast
    } note conc=this [of c1' c2 s' xs]    
     then obtain xs' sa' sa''
       where split:
         "(n,\<Gamma>, (c1', s') # xs') \<in> cptn_mod_nest_call \<and> 
          (xs = map (lift_catch c2) xs' \<or>
          fst (((c1', s') # xs') ! length xs') = Throw \<and>
          snd (last ((c1', s') # xs')) = Normal sa' \<and> s' = Normal sa'' \<and>
          (\<exists>ys. (n,\<Gamma>, (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                xs = map (lift_catch c2) xs' @
                (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<or>
          fst (((c1', s') # xs') ! length xs') = Skip \<and>
          (\<exists>ys. (n,\<Gamma>,(Skip,snd(last ((c1', s')#xs')))#ys) \<in> cptn_mod_nest_call \<and>                   
                 xs=(map (lift_catch c2) xs')@((Skip,snd(last ((c1', s')#xs')))#ys)))"          
        by blast
  then have "(xs = map (lift_catch c2) xs' \<or>
          fst (((c1', s') # xs') ! length xs') = Throw \<and>
          snd (last ((c1', s') # xs')) = Normal sa' \<and> s' = Normal sa'' \<and>
          (\<exists>ys. (n,\<Gamma>, (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                xs = map (lift_catch c2) xs' @
                (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<or>
          fst (((c1', s') # xs') ! length xs') = Skip \<and>
          (\<exists>ys. (n,\<Gamma>,(Skip,snd(last ((c1', s')#xs')))#ys) \<in> cptn_mod_nest_call \<and>                   
                 xs=(map (lift_catch c2) xs')@((Skip,snd(last ((c1', s')#xs')))#ys)))"          
        by auto
  thus ?case 
  proof{           
       assume c1'nonf:"xs = map (lift_catch c2) xs'"
       then have c1'cptn:"(n,\<Gamma>, (c1', s') # xs') \<in> cptn_mod_nest_call" using split by blast
       then have induct_step: "(n, \<Gamma>, (c1, s) # (c1', s')#xs') \<in> cptn_mod_nest_call"
         using Catchc.hyps(2) Catchc.prems(2) SmallStepCon.redex.simps(11) by auto  
       then have "(Catch c1' c2, s')#xs = map (lift_catch c2) ((c1', s')#xs')"
            using c1'nonf
            by (simp add: CptnModCatch1 lift_catch_def)
       thus ?thesis 
            using c1'nonf c1'cptn induct_step 
       by (auto simp add: CptnModNestCatch1)
    next
      assume "fst (((c1', s') # xs') ! length xs') = Throw \<and>
                snd (last ((c1', s') # xs')) = Normal sa' \<and> s' = Normal sa'' \<and>
                (\<exists>ys. (n,\<Gamma>, (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                xs =map (lift_catch c2) xs' @ (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<or>
               fst (((c1', s') # xs') ! length xs') = Skip \<and>
                (\<exists>ys. (n,\<Gamma>,(Skip,snd(last ((c1', s')#xs')))#ys) \<in> cptn_mod_nest_call \<and>                   
                 xs=(map (lift_catch c2) xs')@((Skip,snd(last ((c1', s')#xs')))#ys))"  
      thus ?thesis
      proof
         assume assth:
               "fst (((c1', s') # xs') ! length xs') = Throw \<and>
                snd (last ((c1', s') # xs')) = Normal sa' \<and> s' = Normal sa'' \<and>
                (\<exists>ys. (n,\<Gamma>, (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                xs =map (lift_catch c2) xs' @ (c2, snd (((c1', s') # xs') ! length xs')) # ys)"
             then have s'eqsa'': "s'=Normal sa''" by auto
             then have snormal: "\<exists>ns. s=Normal ns" by (metis Catchc.hyps(1) step_Abrupt_prop step_Fault_prop step_Stuck_prop xstate.exhaust)
             then obtain ys 
             where split':"(n,\<Gamma>, (c2, snd (((c1', s') # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                xs =map (lift_catch c2) xs' @ (c2, snd (((c1', s') # xs') ! length xs')) # ys"
                using assth by auto    
         then have c1'cptn:"(n,\<Gamma>, (c1', s') # xs') \<in> cptn_mod_nest_call" 
              using split by blast
         then have induct_step: "(n,\<Gamma>, (c1, s) # (c1', s')#xs') \<in> cptn_mod_nest_call"
              using Catchc.hyps(2) Catchc.prems(2) SmallStepCon.redex.simps(11) by auto                
         then have seqmap:"(Catch c1 c2, s)#(Catch c1' c2, s')#xs = map (lift_catch c2) ((c1,s)#(c1', s')#xs') @ (c2, snd (((c1', s') # xs') ! length xs')) # ys"
              using split' by (simp add: CptnModCatch3 lift_catch_def) 
        then have lastc1:"last ((c1, s) # (c1', s') # xs') = ((c1', s') # xs') ! length xs'"
             by (simp add: last_length) 
        then have lastc1skip:"fst (last ((c1, s) # (c1', s') # xs')) = Throw" 
             using assth by fastforce
        then have "snd (last ((c1, s) # (c1', s') # xs')) = Normal sa'"
             using assth by force
        thus ?thesis using snormal seqmap s'eqsa'' split' 
              last_length  cptn_mod_nest_call.CptnModNestCatch3 
              induct_step lastc1 lastc1skip
              using Cons_lift_catch_append by fastforce           
    next
        assume assm:" fst (((c1', s') # xs') ! length xs') = Skip \<and> 
                       (\<exists>ys. (n,\<Gamma>,(Skip,snd(last ((c1', s')#xs')))#ys) \<in> cptn_mod_nest_call \<and>                   
                      xs=(map (lift_catch c2) xs')@((Skip,snd(last ((c1', s')#xs')))#ys))"
        then have c1'cptn:"(n,\<Gamma>, (c1', s') # xs') \<in> cptn_mod_nest_call" using split by blast
        then have induct_step: "(n,\<Gamma>, (c1, s) # (c1', s')#xs') \<in> cptn_mod_nest_call"
        using Catchc.hyps(2) Catchc.prems(2) SmallStepCon.redex.simps(11) by auto 
        then have "map (lift_catch c2) ((c1', s') # xs') = (Catch c1' c2, s') # map (lift_catch c2) xs'" 
          by (auto simp add: lift_catch_def)
        then obtain ys 
             where seqmap:"(Catch c1' c2, s')#xs = (map (lift_catch c2) ((c1', s')#xs'))@((Skip,snd(last ((c1', s')#xs')))#ys)"
        using assm by fastforce
        then have lastc1:"last ((c1, s) # (c1', s') # xs') = ((c1', s') # xs') ! length xs'"
                   by (simp add: last_length) 
        then have lastc1skip:"fst (last ((c1, s) # (c1', s') # xs')) = Skip" 
             using assm by fastforce
        then have "snd (last ((c1, s) # (c1', s') # xs')) = snd (last ((c1', s') # xs'))"
             using assm by force
        thus ?thesis 
            using assm c1'cptn induct_step lastc1skip seqmap 
            by (auto simp add:cptn_mod_nest_call.CptnModNestCatch2)
    qed
  }qed              
next
  case (CatchThrowc c2 s)
  have c2incptn:"(n,\<Gamma>, (c2, Normal s) # xs) \<in> cptn_mod_nest_call" by fact
  then have 1:"(n,\<Gamma>, [(Throw, Normal s)]) \<in> cptn_mod_nest_call" 
    by (simp add: cptn_mod_nest_call.CptnModNestOne)
  then have 2:"fst(last ([(Throw, Normal s)])) = Throw" by fastforce
  then have 3:"(n,\<Gamma>,(c2, snd(last [(Throw, Normal s)]))#xs) \<in> cptn_mod_nest_call" 
      using c2incptn by auto  
  then have "(c2,Normal s)#xs=(map (lift c2) [])@(c2, snd(last [(Throw, Normal s)]))#xs" 
       by (auto simp add:lift_def)
  thus ?case using 1 2 3 by (simp add: CptnModNestCatch3)
next
  case (CatchSkipc c2 s)
  have "(n,\<Gamma>, [(Skip, s)]) \<in> cptn_mod_nest_call" 
    by (simp add: cptn_mod_nest_call.CptnModNestOne)
  then obtain ys where 
    ys_nil:"ys=[]" and 
    last:"(n,\<Gamma>, (Skip,  s)#ys)\<in> cptn_mod_nest_call"
    by auto
  moreover have "fst (last ((Skip,  s)#ys)) = Skip" using ys_nil last by auto
  moreover have "snd (last ((Skip,  s)#ys)) = s" using ys_nil last by auto
  moreover from ys_nil have "(map (lift_catch c2) ys) = []" by auto  
  ultimately show ?case using CatchSkipc.prems 
     by simp (simp add: cptn_mod_nest_call.CptnModNestCatch2 ys_nil)
next
  case (FaultPropc c f)
  thus ?case by (simp add: cptn_mod_nest_call.CptnModNestSkip stepc.FaultPropc) 
next
  case (AbruptPropc c f)
  thus ?case by (simp add: cptn_mod_nest_call.CptnModNestSkip stepc.AbruptPropc)
next
  case (StuckPropc c)
  thus ?case by (simp add: cptn_mod_nest_call.CptnModNestSkip stepc.StuckPropc)
qed




lemma not_func_redex_cptn_mod_nest_n_env: 
assumes a0:"\<Gamma>\<turnstile>\<^sub>c (P,s) \<rightarrow>\<^sub>e (P, t)" and
        a1:"(n,\<Gamma>,(P,t)#xs) \<in>  cptn_mod_nest_call"         
shows "(n,\<Gamma>,(P,s)#(P,t)#xs) \<in>  cptn_mod_nest_call"
  by (simp add: a0 a1 cptn_mod_nest_call.CptnModNestEnv)


lemma cptn_mod_nest_cptn_mod:"(n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call  \<Longrightarrow> (\<Gamma>,cfs)\<in> cptn_mod"
by (induct rule:cptn_mod_nest_call.induct, (fastforce simp:cptn_mod.intros )+)


lemma cptn_mod_cptn_mod_nest: "(\<Gamma>,cfs)\<in> cptn_mod \<Longrightarrow> \<exists>n. (n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call"
proof (induct rule:cptn_mod.induct)
   case (CptnModSkip \<Gamma> P s t xs) 
   then obtain n where cptn_nest:"(n, \<Gamma>, (Skip, t) # xs) \<in> cptn_mod_nest_call" by auto   
    {assume asm:"\<forall>f. ((\<exists>sn. s = Normal sn) \<and> (\<Gamma> f) = Some Skip \<longrightarrow> P  \<noteq> Call f  )"     
     then have ?case using CptnModNestSkip[OF CptnModSkip(1) CptnModSkip(2) asm cptn_nest] by auto
    }note t1=this
    {assume asm:"\<not> (\<forall>f. ((\<exists>sn. s = Normal sn) \<and> (\<Gamma> f) = Some Skip \<longrightarrow> P  \<noteq> Call f))"
     then obtain f where asm:"((\<exists>sn. s = Normal sn) \<and> (\<Gamma> f) = Some Skip \<and> P  = Call f)" by auto 
      then obtain sn where normal_s:"s=Normal sn" by auto
     then have t_eq_s:"t=s" using asm cptn_nest normal_s
       by (metis CptnModSkip.hyps(1) LanguageCon.com.simps(22) 
           LanguageCon.inter_guards.simps(79) LanguageCon.inter_guards_Call 
           Pair_inject stepc_Normal_elim_cases(9))
     then have "(Suc n, \<Gamma>,((Call f), Normal sn)#(Skip, Normal sn)#xs) \<in> cptn_mod_nest_call"
       using asm cptn_nest normal_s CptnModNestCall by fastforce        
     then have ?case using asm normal_s t_eq_s by fastforce
    }note t2 = this
    then show ?case using t1 t2 by fastforce  
next
   case (CptnModThrow \<Gamma> P s t xs)  
   then obtain n where cptn_nest:"(n, \<Gamma>, (Throw, t) # xs) \<in> cptn_mod_nest_call" by auto   
    {assume asm:"\<forall>f. ((\<exists>sn. s = Normal sn) \<and> (\<Gamma> f) = Some Throw \<longrightarrow> P  \<noteq> Call f  )"     
     then have ?case using CptnModNestThrow[OF CptnModThrow(1) CptnModThrow(2) asm cptn_nest] by auto
    }note t1=this
    {assume asm:"\<not> (\<forall>f. ((\<exists>sn. s = Normal sn) \<and> (\<Gamma> f) = Some Throw \<longrightarrow> P  \<noteq> Call f))"
     then obtain f where asm:"((\<exists>sn. s = Normal sn) \<and> (\<Gamma> f) = Some Throw \<and> P  = Call f)" by auto 
      then obtain sn where normal_s:"s=Normal sn" by auto
     then have t_eq_s:"t=s" using asm cptn_nest normal_s
       by (metis CptnModThrow.hyps(1) LanguageCon.com.simps(22) 
           LanguageCon.inter_guards.simps(79) LanguageCon.inter_guards_Call 
           Pair_inject stepc_Normal_elim_cases(9))
     then have "(Suc n, \<Gamma>,((Call f), Normal sn)#(Throw, Normal sn)#xs) \<in> cptn_mod_nest_call"
       using asm cptn_nest normal_s CptnModNestCall by fastforce        
     then have ?case using asm normal_s t_eq_s by fastforce
    }note t2 = this
    then show ?case using t1 t2 by fastforce
next
   case (CptnModSeq2 \<Gamma> P0 s xs P1 ys zs) 
   obtain n where n:"(n, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call" using CptnModSeq2(2) by auto
   also obtain m where m:"(m, \<Gamma>, (P1, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call"
     using CptnModSeq2(5) by auto
   ultimately show ?case
   proof (cases "n\<ge>m") 
     case True thus ?thesis  
       using cptn_mod_nest_mono[of m \<Gamma> _ n] m n CptnModSeq2 cptn_mod_nest_call.CptnModNestSeq2 by blast
   next  
     case False 
     thus ?thesis
       using cptn_mod_nest_mono[of n \<Gamma> _ m] m n CptnModSeq2 
             cptn_mod_nest_call.CptnModNestSeq2 le_cases3 by blast      
   qed
next
   case (CptnModSeq3 \<Gamma> P0 s xs s' ys zs P1) 
   obtain n where n:"(n, \<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod_nest_call" using CptnModSeq3(2) by auto
   also obtain m where m:"(m, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call"
     using CptnModSeq3(6) by auto
   ultimately show ?case
   proof (cases "n\<ge>m") 
     case True thus ?thesis  
       using cptn_mod_nest_mono[of m \<Gamma> _ n] m n CptnModSeq3 cptn_mod_nest_call.CptnModNestSeq3
       by fastforce
   next  
     case False 
     thus ?thesis
       using cptn_mod_nest_mono[of n \<Gamma> _ m] m n CptnModSeq3
             cptn_mod_nest_call.CptnModNestSeq3 le_cases3
      proof -
        have f1: "\<not> n \<le> m \<or> (m, \<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod_nest_call"
          by (metis cptn_mod_nest_mono[of n \<Gamma> _ m] n)
        have "n \<le> m"
          using False by linarith
        then have "(m, \<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod_nest_call"
          using f1 by metis
        then show ?thesis
          by (metis (no_types) CptnModSeq3(3) CptnModSeq3(4) CptnModSeq3(7) 
                   cptn_mod_nest_call.CptnModNestSeq3 m)
      qed          
   qed
next
   case (CptnModWhile2 \<Gamma> P s xs b zs ys) 
   obtain n where n:"(n, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call" using CptnModWhile2(2) by auto
   also obtain m where 
     m:" (m, \<Gamma>, (LanguageCon.com.While b P, snd (last ((P, Normal s) # xs))) # ys) \<in> 
          cptn_mod_nest_call"
     using CptnModWhile2(7) by auto
   ultimately show ?case
   proof (cases "n\<ge>m") 
     case True thus ?thesis  
       using cptn_mod_nest_mono[of m \<Gamma> _ n] m n 
             CptnModWhile2 cptn_mod_nest_call.CptnModNestWhile2 by metis
   next  
     case False 
     thus ?thesis       
    proof -
      have f1: "\<not> n \<le> m \<or> (m, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call"
        using cptn_mod_nest_mono[of n \<Gamma> _ m] n by presburger
      have "n \<le> m"
        using False by linarith
      then have "(m, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call"
        using f1 by metis
      then show ?thesis
        by (metis (no_types) CptnModWhile2(3) CptnModWhile2(4) CptnModWhile2(5) 
                  cptn_mod_nest_call.CptnModNestWhile2 m)
    qed 
   qed
next
   case (CptnModWhile3 \<Gamma> P s xs b s' ys zs)
   obtain n where n:"(n, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call" 
     using CptnModWhile3(2) by auto
   also obtain m where 
     m:" (m, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call"
     using CptnModWhile3(7) by auto
   ultimately show ?case
   proof (cases "n\<ge>m") 
     case True thus ?thesis  
     proof -
      have "(n, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call"
        using True cptn_mod_nest_mono[of m \<Gamma> _ n] m by presburger
      then show ?thesis
        by (metis (no_types) CptnModWhile3.hyps(3) CptnModWhile3.hyps(4) 
            CptnModWhile3.hyps(5) CptnModWhile3.hyps(8) cptn_mod_nest_call.CptnModNestWhile3 n)
     qed 
   next  
     case False 
     thus ?thesis  using m n cptn_mod_nest_call.CptnModNestWhile3 cptn_mod_nest_mono[of n \<Gamma> _ m]
       by (metis CptnModWhile3.hyps(3) CptnModWhile3.hyps(4) 
           CptnModWhile3.hyps(5) CptnModWhile3.hyps(8) le_cases)
   qed
next
  case (CptnModCatch2 \<Gamma> P0 s xs ys zs P1) 
  obtain n where n:"(n, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call" using CptnModCatch2(2) by auto
   also obtain m where m:"(m, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call"
     using CptnModCatch2(5) by auto
   ultimately show ?case
   proof (cases "n\<ge>m") 
     case True thus ?thesis  
       using cptn_mod_nest_mono[of m \<Gamma> _ n] m n 
             CptnModCatch2 cptn_mod_nest_call.CptnModNestCatch2 by blast
   next  
     case False 
     thus ?thesis
       using cptn_mod_nest_mono[of n \<Gamma> _ m] m n CptnModCatch2 
             cptn_mod_nest_call.CptnModNestCatch2 le_cases3 by blast      
   qed
next
  case (CptnModCatch3 \<Gamma> P0 s xs s' ys zs P1) 
   obtain n where n:"(n, \<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod_nest_call" 
     using CptnModCatch3(2) by auto
   also obtain m where m:"(m, \<Gamma>, (ys, snd (last ((P0, Normal s) # xs))) # zs) \<in> cptn_mod_nest_call"
     using CptnModCatch3(6) by auto
   ultimately show ?case
   proof (cases "n\<ge>m") 
     case True thus ?thesis  
       using cptn_mod_nest_mono[of m \<Gamma> _ n] m n CptnModCatch3 cptn_mod_nest_call.CptnModNestCatch3
       by fastforce
   next  
     case False 
     thus ?thesis
       using cptn_mod_nest_mono[of n \<Gamma> _ m] m n CptnModCatch3 
             cptn_mod_nest_call.CptnModNestCatch3 le_cases3
      proof -
        have f1: "\<not> n \<le> m \<or> (m, \<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod_nest_call"
          using \<open>\<And>cfs. \<lbrakk>(n, \<Gamma>, cfs) \<in> cptn_mod_nest_call; n \<le> m\<rbrakk> \<Longrightarrow> (m, \<Gamma>, cfs) \<in> cptn_mod_nest_call\<close> n by presburger
        have "n \<le> m"
          using False by auto
        then have "(m, \<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod_nest_call"
          using f1 by meson
        then show ?thesis
          by (metis (no_types) \<open>P1 = map (lift_catch ys) xs @ (ys, snd (last ((P0, Normal s) # xs))) # zs\<close> \<open>fst (last ((P0, Normal s) # xs)) = LanguageCon.com.Throw\<close> \<open>snd (last ((P0, Normal s) # xs)) = Normal s'\<close> cptn_mod_nest_call.CptnModNestCatch3 m)
      qed      
   qed
qed(fastforce intro: cptn_mod_nest_call.intros)+

lemma cptn_mod_eq_cptn_mod_nest:
  "(\<Gamma>,cfs)\<in> cptn_mod \<longleftrightarrow> (\<exists>n. (n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call)"
  using cptn_mod_cptn_mod_nest cptn_mod_nest_cptn_mod by auto

lemma cptn_mod_eq_cptn_mod_nest':
  "\<exists>n. ((\<Gamma>,cfs)\<in> cptn_mod \<longleftrightarrow> (n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call)"
  using cptn_mod_eq_cptn_mod_nest by auto

lemma cptn_mod_eq_cptn_mod_nest1:
  "(\<Gamma>,cfs)\<in> cptn_mod = (\<exists>n. (n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call)"
  using cptn_mod_cptn_mod_nest cptn_mod_nest_cptn_mod by auto


lemma cptn_eq_cptn_mod_nest:
  "(\<Gamma>,cfs)\<in> cptn = (\<exists>n. (n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call)"
  using cptn_eq_cptn_mod_set cptn_mod_cptn_mod_nest cptn_mod_nest_cptn_mod by blast


subsection \<open>computation on nested calls limit\<close>
subsection \<open>Elimination theorems\<close>
lemma mod_env_not_component:
shows    "\<not> \<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow> (P, t)"
proof 
  assume a3:"\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow> (P, t)"           
  thus  False using step_change_p_or_eq_s a3 by fastforce
qed

lemma elim_cptn_mod_nest_step_c:
 assumes a0:"(n,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" and
         a1:"cfg = (P,s)#(Q,t)#cfg1"         
 shows "\<Gamma>\<turnstile>\<^sub>c (P,s) \<rightarrow> (Q,t) \<or> \<Gamma>\<turnstile>\<^sub>c (P,s) \<rightarrow>\<^sub>e (Q,t)"
proof-
  have "(\<Gamma>,cfg) \<in>  cptn" using a0 cptn_mod_nest_cptn_mod
    using cptn_eq_cptn_mod_set by auto 
  then have "\<Gamma>\<turnstile>\<^sub>c (P,s) \<rightarrow>\<^sub>c\<^sub>e (Q,t)" using a1
    by (metis c_step cptn_elim_cases(2) e_step)
  thus ?thesis
    using step_ce_not_step_e_step_c by blast  
qed

lemma elim_cptn_mod_nest_call_env:
 assumes a0:"(n,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" and
         a1:"cfg = (P,s)#(P,t)#cfg1"  and
         a2:"\<forall>f. \<Gamma> f = Some (LanguageCon.com.Call f) \<and> 
                 (\<exists>sn. s = Normal sn) \<and> s = t \<longrightarrow> SmallStepCon.redex P \<noteq> LanguageCon.com.Call f"
 shows "(n,\<Gamma>,(P,t)#cfg1) \<in>  cptn_mod_nest_call"
 using a0 a1 a2
proof (induct arbitrary: P cfg1 s t rule:cptn_mod_nest_call.induct ) 
case (CptnModNestSeq1 n \<Gamma> P0 sa xs zs P1)
   then obtain xs' where "xs =  (P0, t)#xs'" unfolding lift_def by fastforce
   then have step:"(n, \<Gamma>, (P0, t) # xs') \<in> cptn_mod_nest_call" using CptnModNestSeq1 by fastforce        
   have "(P, t) = lift P1 (P0, t) \<and> cfg1 = map (lift P1) xs'"
      using CptnModNestSeq1.hyps(3) CptnModNestSeq1.prems(1) \<open>xs = (P0, t) # xs'\<close> by auto
    then have "(n, \<Gamma>, (LanguageCon.com.Seq P0 P1, t) # cfg1) \<in> cptn_mod_nest_call"
      by (meson cptn_mod_nest_call.CptnModNestSeq1 local.step)
    then show ?case
      using CptnModNestSeq1.prems(1) by fastforce  
next
  case (CptnModNestSeq2 n \<Gamma> P0 sa xs P1 ys zs) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs') 
    then have x:"x=(P0,t)" 
    proof-
      have "zs=(Seq P0 P1,t)#cfg1" using Cons by fastforce
      thus ?thesis using Cons(7) unfolding lift_def
      proof -
        assume "zs = map (\<lambda>a. case a of (P, s) \<Rightarrow> (LanguageCon.com.Seq P P1, s)) (x # xs') @ 
                     (P1, snd (last ((P0, sa) # x # xs'))) # ys"
        then have "LanguageCon.com.Seq (fst x) P1 = LanguageCon.com.Seq P0 P1 \<and> snd x = t"
          by (simp add: \<open>zs = (LanguageCon.com.Seq P0 P1, t) # cfg1\<close> case_prod_beta)
        then show ?thesis
          by fastforce
      qed 
    qed
    then have step:"(n, \<Gamma>, (P0, t) # xs') \<in> cptn_mod_nest_call" using Cons by fastforce         
    have "fst (last ((P0, t) # xs')) = LanguageCon.com.Skip"
      using Cons.prems(3) \<open>x = (P0, t)\<close> by force
    then show ?case
      using Cons.prems(4) Cons.prems(6) CptnModNestSeq2.prems(1) x 
            cptn_mod_nest_call.CptnModNestSeq2 local.step by fastforce
  qed          
next 
  case (CptnModNestSeq3 n \<Gamma> P0 sa xs s' ys zs P1) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs') 
    then have x:"x=(P0,t)" 
    proof-
      have zs:"zs=(Seq P0 P1,t)#cfg1" using Cons by fastforce
      have "(LanguageCon.com.Seq (fst x) P1, snd x) = lift P1 x"
         by (simp add: lift_def prod.case_eq_if)
      then have "LanguageCon.com.Seq (fst x) P1 = LanguageCon.com.Seq P0 P1 \<and> snd x = t"
         using Cons.prems(7) zs by force
      then show ?thesis
          by fastforce                
    qed
    then have step:"(n, \<Gamma>, (P0, t) # xs') \<in> cptn_mod_nest_call" using Cons by fastforce         
    then obtain t' where t:"t=Normal t'" 
      using Normal_Normal Cons(2) Cons(5) cptn_mod_nest_cptn_mod cptn_eq_cptn_mod_set x
      by (metis snd_eqD)
    then show ?case using x Cons(5) Cons(6) cptn_mod_nest_call.CptnModNestSeq3 step
    proof -
      have "last ((P0, Normal t') # xs') = last ((P0, Normal sa) # x # xs')"
        using t x by force
      then have "fst (last ((P0, Normal t') # xs')) = LanguageCon.com.Throw"
        using Cons.prems(3) by presburger
      then show ?thesis
        using Cons.prems(4) Cons.prems(5) Cons.prems(7) 
              CptnModNestSeq3.prems(1) cptn_mod_nest_call.CptnModNestSeq3 
              local.step t x by fastforce
    qed       
  qed       
next
  case (CptnModNestCatch1 n \<Gamma> P0 s xs zs P1) 
   then obtain xs' where "xs =  (P0, t)#xs'" unfolding lift_catch_def by fastforce
   then have step:"(n, \<Gamma>, (P0, t) # xs') \<in> cptn_mod_nest_call" using CptnModNestCatch1 by fastforce        
   have "(P, t) = lift_catch P1 (P0, t) \<and> cfg1 = map (lift_catch P1) xs'"
      using CptnModNestCatch1.hyps(3) CptnModNestCatch1.prems(1) \<open>xs = (P0, t) # xs'\<close> by auto
    then have "(n, \<Gamma>, (Catch P0 P1, t) # cfg1) \<in> cptn_mod_nest_call"
      by (meson cptn_mod_nest_call.CptnModNestCatch1 local.step)
    then show ?case
      using CptnModNestCatch1.prems(1) by fastforce  
next
  case (CptnModNestCatch2 n \<Gamma> P0 sa xs ys zs P1) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs') 
    then have x:"x=(P0,t)" 
    proof-
      have zs:"zs=(Catch P0 P1,t)#cfg1" using Cons by fastforce
      have "(LanguageCon.com.Catch (fst x) P1, snd x) = lift_catch P1 x"
         by (simp add: lift_catch_def prod.case_eq_if)
      then have "LanguageCon.com.Catch (fst x) P1 = LanguageCon.com.Catch P0 P1 \<and> snd x = t"
         using Cons.prems(6) zs by fastforce           
      then show ?thesis
          by fastforce                
    qed
    then have step:"(n, \<Gamma>, (P0, t) # xs') \<in> cptn_mod_nest_call" using Cons by fastforce             
    have "fst (last ((P0, t) # xs')) = LanguageCon.com.Skip"
      using Cons.prems(3) x by auto
    then show ?case
      using Cons.prems(4) Cons.prems(6) CptnModNestCatch2.prems(1) 
            cptn_mod_nest_call.CptnModNestCatch2 local.step x by fastforce 
  qed          
next
  case (CptnModNestCatch3 n \<Gamma> P0 sa xs s' P1 ys zs) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs')
    then have x:"x=(P0,t)" 
    proof-
      have zs:"zs=(Catch P0 P1,t)#cfg1" using Cons by fastforce
      thus ?thesis using Cons(8) lift_catch_def unfolding lift_def
      proof -
        assume "zs = map (lift_catch P1) (x # xs') @ (P1, snd (last ((P0, Normal sa) # x # xs'))) # ys"
        then have "LanguageCon.com.Catch (fst x) P1 = LanguageCon.com.Catch P0 P1 \<and> snd x = t"
          by (simp add: case_prod_unfold lift_catch_def zs)          
        then show ?thesis
          by fastforce
      qed 
    qed
    then have step:"(n, \<Gamma>, (P0, t) # xs') \<in> cptn_mod_nest_call" using Cons by fastforce
    then obtain t' where t:"t=Normal t'" 
      using Normal_Normal Cons(2) Cons(5) cptn_mod_nest_cptn_mod cptn_eq_cptn_mod_set x
      by (metis snd_eqD)
    then show ?case 
    proof -
      have "last ((P0, Normal t') # xs') = last ((P0, Normal sa) # x # xs')"
        using t x by force
      then have "fst (last ((P0, Normal t') # xs')) = LanguageCon.com.Throw"
        using Cons.prems(3) by presburger
      then show ?thesis
        using Cons.prems(4) Cons.prems(5) Cons.prems(7) 
              CptnModNestCatch3.prems(1) cptn_mod_nest_call.CptnModNestCatch3 
              local.step t x by fastforce
    qed
  qed   
qed(fastforce+)


lemma elim_cptn_mod_nest_not_env_call:
 assumes a0:"(n,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" and
         a1:"cfg = (P,s)#(Q,t)#cfg1" and
         a2:"(\<forall>f. redex P \<noteq> Call f) \<or>  
             SmallStepCon.redex P = LanguageCon.com.Call fn \<and> \<Gamma> fn = None \<or>
            (redex P = Call fn \<and> (\<forall>sa. s\<noteq>Normal sa))"  
 shows "(n,\<Gamma>,(Q,t)#cfg1) \<in>  cptn_mod_nest_call"
 using a0 a1 a2
proof (induct arbitrary: P Q cfg1 s t rule:cptn_mod_nest_call.induct )
case (CptnModNestSeq1 n \<Gamma> P0 s xs zs P1)
   then obtain P0' xs' where "xs =  (P0', t)#xs'" unfolding lift_def by fastforce
   then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call" using CptnModNestSeq1 by fastforce        
   have Q:"(Q, t) = lift P1 (P0', t) \<and> cfg1 = map (lift P1) xs'"
     using CptnModNestSeq1.hyps(3) CptnModNestSeq1.prems(1) \<open>xs = (P0', t) # xs'\<close> by auto
   also then have "(n, \<Gamma>, (LanguageCon.com.Seq P0' P1, t) # cfg1) \<in> cptn_mod_nest_call"
     by (meson cptn_mod_nest_call.CptnModNestSeq1 local.step)
   ultimately show ?case
     using CptnModNestSeq1.prems(1)
     by (simp add: Cons_lift Q)   
next
  case (CptnModNestSeq2 n \<Gamma> P0 sa xs P1 ys zs) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs')
    then have x:"\<exists>P0'. x=(P0',t)" 
    proof-
      obtain P0'' where zs: "zs=(Seq P0'' P1,t)#cfg1" using Cons(7) Cons(8) 
        unfolding lift_def by (simp add: Cons_eq_append_conv case_prod_beta') 
      thus ?thesis using Cons(7) unfolding lift_def
      proof -
        assume "zs = map (\<lambda>a. case a of (P, s) \<Rightarrow> (LanguageCon.com.Seq P P1, s)) (x # xs') @ 
                     (P1, snd (last ((P0, sa) # x # xs'))) # ys"
        then have "LanguageCon.com.Seq (fst x) P1 = LanguageCon.com.Seq P0'' P1 \<and> snd x = t"
          by (simp add: zs case_prod_beta)
        also have "sa=s" using Cons by fastforce
        ultimately show ?thesis by (meson eq_snd_iff)           
      qed 
    qed
    then obtain P0' where x:"x=(P0',t)" by auto
    then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call" using Cons by force
    have "fst (last ((P0', t) # xs')) = LanguageCon.com.Skip"
      using Cons.prems(3) x by force
    then show ?case
      using Cons.prems(4) Cons.prems(6) CptnModNestSeq2.prems(1) x 
           local.step cptn_mod_nest_call.CptnModNestSeq2[of n \<Gamma> P0' t xs' P1 ys] Cons_lift_append
           by (metis (no_types, lifting) last_ConsR list.inject list.simps(3))        
  qed          
next 
  case (CptnModNestSeq3 n \<Gamma> P0 sa xs s' ys zs P1) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs') 
    then have x:"\<exists>P0'. x=(P0',t)"
    proof-
      obtain P0' where zs:"zs=(Seq P0' P1,t)#cfg1" using Cons(8) Cons(9) 
        unfolding lift_def
        unfolding lift_def by (simp add: Cons_eq_append_conv case_prod_beta')
      have "(LanguageCon.com.Seq (fst x) P1, snd x) = lift P1 x"
         by (simp add: lift_def prod.case_eq_if)
      then have "LanguageCon.com.Seq (fst x) P1 = LanguageCon.com.Seq P0' P1 \<and> snd x = t"
         using zs by (simp add: Cons.prems(7)) 
      then show ?thesis by (meson eq_snd_iff)                        
    qed
    then obtain P0' where x:"x=(P0',t)" by auto
    then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call"
    proof -
      have f1: "LanguageCon.com.Seq P0 P1 = P \<and> Normal sa = s"
        using CptnModNestSeq3.prems(1) by blast
      then have "SmallStepCon.redex P = SmallStepCon.redex P0"
        by (metis SmallStepCon.redex.simps(4))
      then show ?thesis
        using f1 Cons.prems(2) CptnModNestSeq3.prems(2) x by presburger
    qed      
    then obtain t' where t:"t=Normal t'" 
      using Normal_Normal Cons(2) Cons(5) cptn_mod_nest_cptn_mod cptn_eq_cptn_mod_set x
      by (metis snd_eqD)
    then show ?case using x Cons(5) Cons(6) cptn_mod_nest_call.CptnModNestSeq3 step
    proof -
      have "last ((P0', Normal t') # xs') = last ((P0, Normal sa) # x # xs')"
        using t x by force
      also then have "fst (last ((P0', Normal t') # xs')) = LanguageCon.com.Throw"
        using Cons.prems(3) by presburger
      ultimately show ?thesis
        using Cons.prems(4) Cons.prems(5) Cons.prems(7) 
              CptnModNestSeq3.prems(1) cptn_mod_nest_call.CptnModNestSeq3[of n \<Gamma> P0' t' xs' s' ys] 
              local.step t x  Cons_lift_append
      by (metis (no_types, lifting) list.sel(3))               
    qed       
  qed       
next
  case (CptnModNestCatch1 n \<Gamma> P0 s xs zs P1) 
   then obtain P0' xs' where xs:"xs =  (P0', t)#xs'" unfolding lift_catch_def by fastforce
   then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call" using CptnModNestCatch1 by fastforce        
   have Q:"(Q, t) = lift_catch P1 (P0', t) \<and> cfg1 = map (lift_catch P1) xs'"
      using CptnModNestCatch1.hyps(3) CptnModNestCatch1.prems(1) xs by auto
    then have "(n, \<Gamma>, (Catch P0' P1, t) # cfg1) \<in> cptn_mod_nest_call"
      by (meson cptn_mod_nest_call.CptnModNestCatch1 local.step)
    then show ?case
      using CptnModNestCatch1.prems(1) by (simp add:Cons_lift_catch Q)
next
  case (CptnModNestCatch2 n \<Gamma> P0 sa xs ys zs P1) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs') 
    then have x:"\<exists>P0'. x=(P0',t)" 
    proof-
      obtain P0' where zs:"zs=(Catch P0' P1,t)#cfg1" using Cons unfolding lift_catch_def
        by (simp add: case_prod_unfold)
      have "(LanguageCon.com.Catch (fst x) P1, snd x) = lift_catch P1 x"
         by (simp add: lift_catch_def prod.case_eq_if)
      then have "LanguageCon.com.Catch (fst x) P1 = LanguageCon.com.Catch P0' P1 \<and> snd x = t"
         using Cons.prems(6) zs by fastforce           
      then show ?thesis by (meson eq_snd_iff)          
    qed
    then obtain P0' where x:"x=(P0',t)" by auto
    then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call"     
      using Cons.prems(2) CptnModNestCatch2.prems(1) CptnModNestCatch2.prems(2) x by force

    have skip:"fst (last ((P0', t) # xs')) = LanguageCon.com.Skip"
      using Cons.prems(3) x by auto
    show ?case
    proof -
      have "(P, s) # (Q, t) # cfg1 = (LanguageCon.com.Catch P0 P1, sa) # map (lift_catch P1) (x # xs') @ 
              (LanguageCon.com.Skip, snd (last ((P0, sa) # x # xs'))) # ys"
        using CptnModNestCatch2.prems  Cons.prems(6) by auto
      then show ?thesis 
        using Cons_lift_catch_append Cons.prems(4) 
              cptn_mod_nest_call.CptnModNestCatch2[OF local.step skip] last.simps list.distinct(1)
              x 
        by (metis (no_types)  list.sel(3) x)
    qed
  qed          
next
  case (CptnModNestCatch3 n \<Gamma> P0 sa xs s' P1 ys zs) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs')
    then have x:"\<exists>P0'. x=(P0',t)" 
    proof-
      obtain P0' where zs:"zs=(Catch P0' P1,t)#cfg1" using Cons unfolding lift_catch_def
        by (simp add: case_prod_unfold)
      thus ?thesis using Cons(8) lift_catch_def unfolding lift_def
      proof -
        assume "zs = map (lift_catch P1) (x # xs') @ (P1, snd (last ((P0, Normal sa) # x # xs'))) # ys"
        then have "LanguageCon.com.Catch (fst x) P1 = LanguageCon.com.Catch P0' P1 \<and> snd x = t"
          by (simp add: case_prod_unfold lift_catch_def zs)          
        then show ?thesis by (meson eq_snd_iff)  
      qed 
    qed
    then obtain P0' where x:"x=(P0',t)" by auto
    then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call" using Cons
      using Cons.prems(2) CptnModNestCatch3.prems(1) CptnModNestCatch3.prems(2) x by force
    then obtain t' where t:"t=Normal t'" 
      using Normal_Normal Cons(2) Cons(5) cptn_mod_nest_cptn_mod cptn_eq_cptn_mod_set x
      by (metis snd_eqD)
    then show ?case 
    proof -
      have "last ((P0', Normal t') # xs') = last ((P0, Normal sa) # x # xs')"
        using t x by force
      also then have "fst (last ((P0', Normal t') # xs')) = LanguageCon.com.Throw"
        using Cons.prems(3) by presburger
      ultimately show ?thesis
        using Cons.prems(4) Cons.prems(5) Cons.prems(7) 
              CptnModNestCatch3.prems(1) cptn_mod_nest_call.CptnModNestCatch3[of n \<Gamma> P0' t' xs' s' P1] 
              local.step t x by (metis Cons_lift_catch_append list.sel(3)) 
    qed
  qed
next
case (CptnModNestWhile1 n \<Gamma> P0 s' xs b zs) 
  thus ?case
   using cptn_mod_nest_call.CptnModNestSeq1 list.inject by blast   
next
  case (CptnModNestWhile2 n \<Gamma> P0 s' xs b zs ys)  
  have "(LanguageCon.com.While b P0, Normal s') = (P, s) \<and> 
        (LanguageCon.com.Seq P0 (LanguageCon.com.While b P0), Normal s') # zs = (Q, t) # cfg1"
    using CptnModNestWhile2.prems by fastforce
  then show ?case
    using CptnModNestWhile2.hyps(1) CptnModNestWhile2.hyps(3) 
          CptnModNestWhile2.hyps(5) CptnModNestWhile2.hyps(6) 
          cptn_mod_nest_call.CptnModNestSeq2 by blast
next
  case (CptnModNestWhile3 n \<Gamma> P0 s' xs b zs) thus ?case
    by (metis (no_types) CptnModNestWhile3.hyps(1) CptnModNestWhile3.hyps(3) CptnModNestWhile3.hyps(5) 
                         CptnModNestWhile3.hyps(6) CptnModNestWhile3.hyps(8) CptnModNestWhile3.prems 
                         cptn_mod_nest_call.CptnModNestSeq3 list.inject)  
qed(fastforce+)

inductive_cases stepc_call_skip_normal:
 "\<Gamma>\<turnstile>\<^sub>c(Call p,Normal s) \<rightarrow> (Skip,s')"

lemma elim_cptn_mod_nest_call_n_greater_zero:
 assumes a0:"(n,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" and
         a1:"cfg = (P,Normal s)#(Q,t)#cfg1 \<and> P = Call f \<and> \<Gamma> f = Some Q \<and> P\<noteq>Q"
 shows  "n>0" 
  using a0 a1 by (induct rule:cptn_mod_nest_call.induct, fastforce+)


lemma elim_cptn_mod_nest_call_0_False:
 assumes a0:"(0,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" and
         a1:"cfg = (P,Normal s)#(Q,t)#cfg1 \<and> P = Call f \<and> \<Gamma> f = Some Q \<and> P\<noteq>Q"
shows "PP"
using a0 a1 elim_cptn_mod_nest_call_n_greater_zero 
by fastforce

lemma elim_cptn_mod_nest_call_n_dec1:
 assumes a0:"(n,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" and
         a1:"cfg = (P,Normal s)#(Q,t)#cfg1 \<and> P = Call f \<and> \<Gamma> f = Some Q \<and> t= Normal s \<and> P\<noteq>Q"
 shows "(n-1,\<Gamma>,(Q,t)#cfg1) \<in>  cptn_mod_nest_call"
 using a0 a1 
  by (induct rule:cptn_mod_nest_call.induct,fastforce+)

lemma elim_cptn_mod_nest_call_n_dec:
 assumes a0:"(n,\<Gamma>,(Call f,Normal s)#(the (\<Gamma> f),Normal s)#cfg1) \<in>  cptn_mod_nest_call" and
         a1:"\<Gamma> f = Some Q " and a2:"Call f\<noteq>the (\<Gamma> f)"
       shows "(n-1,\<Gamma>,(the (\<Gamma> f),Normal s)#cfg1) \<in>  cptn_mod_nest_call"
  using elim_cptn_mod_nest_call_n_dec1
 using a0 a1 a2
  by fastforce


lemma elim_cptn_mod_nest_call_n:
 assumes a0:"(n,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" and
         a1:"cfg = (P, s)#(Q,t)#cfg1"          
 shows "(n,\<Gamma>,(Q,t)#cfg1) \<in>  cptn_mod_nest_call"
 using a0 a1 
proof (induct arbitrary: P Q cfg1 s t rule:cptn_mod_nest_call.induct )
case (CptnModNestCall n \<Gamma> bdy sa ys p)
  thus ?case using cptn_mod_nest_mono1 list.inject by blast
next 
case (CptnModNestSeq1 n \<Gamma> P0 s xs zs P1) 
   then obtain P0' xs' where "xs =  (P0', t)#xs'" unfolding lift_def by fastforce
   then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call" using CptnModNestSeq1 by fastforce        
   have Q:"(Q, t) = lift P1 (P0', t) \<and> cfg1 = map (lift P1) xs'"
     using CptnModNestSeq1.hyps(3) CptnModNestSeq1.prems(1) \<open>xs = (P0', t) # xs'\<close> by auto
   also then have "(n, \<Gamma>, (LanguageCon.com.Seq P0' P1, t) # cfg1) \<in> cptn_mod_nest_call"
     by (meson cptn_mod_nest_call.CptnModNestSeq1 local.step)
   ultimately show ?case
     using CptnModNestSeq1.prems(1)
     by (simp add: Cons_lift Q)   
next
  case (CptnModNestSeq2 n \<Gamma> P0 sa xs P1 ys zs) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs')
    then have x:"\<exists>P0'. x=(P0',t)" 
    proof-
      obtain P0'' where zs: "zs=(Seq P0'' P1,t)#cfg1" using Cons(7) Cons(8) 
        unfolding lift_def by (simp add: Cons_eq_append_conv case_prod_beta') 
      thus ?thesis using Cons(7) unfolding lift_def
      proof -
        assume "zs = map (\<lambda>a. case a of (P, s) \<Rightarrow> (LanguageCon.com.Seq P P1, s)) (x # xs') @ 
                     (P1, snd (last ((P0, sa) # x # xs'))) # ys"
        then have "LanguageCon.com.Seq (fst x) P1 = LanguageCon.com.Seq P0'' P1 \<and> snd x = t"
          by (simp add: zs case_prod_beta)
        also have "sa=s" using Cons by fastforce
        ultimately show ?thesis by (meson eq_snd_iff)           
      qed 
    qed
    then obtain P0' where x:"x=(P0',t)" by auto
    then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call" using Cons by force
    have "fst (last ((P0', t) # xs')) = LanguageCon.com.Skip"
      using Cons.prems(3) x by force
    then show ?case
      using Cons.prems(4) Cons.prems(6) CptnModNestSeq2.prems(1) x 
           local.step cptn_mod_nest_call.CptnModNestSeq2[of n \<Gamma> P0' t xs' P1 ys] Cons_lift_append
           by (metis (no_types, lifting) last_ConsR list.inject list.simps(3))        
  qed          
next 
  case (CptnModNestSeq3 n \<Gamma> P0 sa xs s' ys zs P1) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs') 
    then have x:"\<exists>P0'. x=(P0',t)"
    proof-
      obtain P0' where zs:"zs=(Seq P0' P1,t)#cfg1" using Cons(8) Cons(9) 
        unfolding lift_def
        unfolding lift_def by (simp add: Cons_eq_append_conv case_prod_beta')
      have "(LanguageCon.com.Seq (fst x) P1, snd x) = lift P1 x"
         by (simp add: lift_def prod.case_eq_if)
      then have "LanguageCon.com.Seq (fst x) P1 = LanguageCon.com.Seq P0' P1 \<and> snd x = t"
         using zs by (simp add: Cons.prems(7)) 
      then show ?thesis by (meson eq_snd_iff)                        
    qed
    then obtain P0' where x:"x=(P0',t)" by auto
    then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call" using Cons by fastforce         
    then obtain t' where t:"t=Normal t'" 
      using Normal_Normal Cons(2) Cons(5) cptn_mod_nest_cptn_mod cptn_eq_cptn_mod_set x
      by (metis snd_eqD)
    then show ?case using x Cons(5) Cons(6) cptn_mod_nest_call.CptnModNestSeq3 step
    proof -
      have "last ((P0', Normal t') # xs') = last ((P0, Normal sa) # x # xs')"
        using t x by force
      also then have "fst (last ((P0', Normal t') # xs')) = LanguageCon.com.Throw"
        using Cons.prems(3) by presburger
      ultimately show ?thesis
        using Cons.prems(4) Cons.prems(5) Cons.prems(7) 
              CptnModNestSeq3.prems(1) cptn_mod_nest_call.CptnModNestSeq3[of n \<Gamma> P0' t' xs' s' ys] 
              local.step t x  Cons_lift_append
      by (metis (no_types, lifting) list.sel(3))               
    qed       
  qed       
next
  case (CptnModNestCatch1 n \<Gamma> P0 s xs zs P1) 
   then obtain P0' xs' where xs:"xs =  (P0', t)#xs'" unfolding lift_catch_def by fastforce
   then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call" using CptnModNestCatch1 by fastforce        
   have Q:"(Q, t) = lift_catch P1 (P0', t) \<and> cfg1 = map (lift_catch P1) xs'"
      using CptnModNestCatch1.hyps(3) CptnModNestCatch1.prems(1) xs by auto
    then have "(n, \<Gamma>, (Catch P0' P1, t) # cfg1) \<in> cptn_mod_nest_call"
      by (meson cptn_mod_nest_call.CptnModNestCatch1 local.step)
    then show ?case
      using CptnModNestCatch1.prems(1) by (simp add:Cons_lift_catch Q)
next
  case (CptnModNestCatch2 n \<Gamma> P0 sa xs ys zs P1) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs') 
    then have x:"\<exists>P0'. x=(P0',t)" 
    proof-
      obtain P0' where zs:"zs=(Catch P0' P1,t)#cfg1" using Cons unfolding lift_catch_def
        by (simp add: case_prod_unfold)
      have "(LanguageCon.com.Catch (fst x) P1, snd x) = lift_catch P1 x"
         by (simp add: lift_catch_def prod.case_eq_if)
      then have "LanguageCon.com.Catch (fst x) P1 = LanguageCon.com.Catch P0' P1 \<and> snd x = t"
         using Cons.prems(6) zs by fastforce           
      then show ?thesis by (meson eq_snd_iff)          
    qed
    then obtain P0' where x:"x=(P0',t)" by auto
    then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call" using Cons by fastforce             
    have skip:"fst (last ((P0', t) # xs')) = LanguageCon.com.Skip"
      using Cons.prems(3) x by auto
    show ?case
    proof -
      have "(P, s) # (Q, t) # cfg1 = (LanguageCon.com.Catch P0 P1, sa) # map (lift_catch P1) (x # xs') @ 
              (LanguageCon.com.Skip, snd (last ((P0, sa) # x # xs'))) # ys"
        using CptnModNestCatch2.prems  Cons.prems(6) by auto
      then show ?thesis 
        using Cons_lift_catch_append Cons.prems(4) 
              cptn_mod_nest_call.CptnModNestCatch2[OF local.step skip] last.simps list.distinct(1)
              x 
        by (metis (no_types)  list.sel(3) x)
    qed
  qed          
next
  case (CptnModNestCatch3 n \<Gamma> P0 sa xs s' P1 ys zs) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs')
    then have x:"\<exists>P0'. x=(P0',t)" 
    proof-
      obtain P0' where zs:"zs=(Catch P0' P1,t)#cfg1" using Cons unfolding lift_catch_def
        by (simp add: case_prod_unfold)
      thus ?thesis using Cons(8) lift_catch_def unfolding lift_def
      proof -
        assume "zs = map (lift_catch P1) (x # xs') @ (P1, snd (last ((P0, Normal sa) # x # xs'))) # ys"
        then have "LanguageCon.com.Catch (fst x) P1 = LanguageCon.com.Catch P0' P1 \<and> snd x = t"
          by (simp add: case_prod_unfold lift_catch_def zs)          
        then show ?thesis by (meson eq_snd_iff)  
      qed 
    qed
    then obtain P0' where x:"x=(P0',t)" by auto
    then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call" using Cons by fastforce
    then obtain t' where t:"t=Normal t'" 
      using Normal_Normal Cons(2) Cons(5) cptn_mod_nest_cptn_mod cptn_eq_cptn_mod_set x
      by (metis snd_eqD)
    then show ?case 
    proof -
      have "last ((P0', Normal t') # xs') = last ((P0, Normal sa) # x # xs')"
        using t x by force
      also then have "fst (last ((P0', Normal t') # xs')) = LanguageCon.com.Throw"
        using Cons.prems(3) by presburger
      ultimately show ?thesis
        using Cons.prems(4) Cons.prems(5) Cons.prems(7) 
              CptnModNestCatch3.prems(1) cptn_mod_nest_call.CptnModNestCatch3[of n \<Gamma> P0' t' xs' s' P1] 
              local.step t x by (metis Cons_lift_catch_append list.sel(3)) 
    qed
  qed
next
case (CptnModNestWhile1 n \<Gamma> P0 s' xs b zs) 
  thus ?case
   using cptn_mod_nest_call.CptnModNestSeq1 list.inject by blast   
next
  case (CptnModNestWhile2 n \<Gamma> P0 s' xs b zs ys)  
  have "(LanguageCon.com.While b P0, Normal s') = (P, s) \<and> 
        (LanguageCon.com.Seq P0 (LanguageCon.com.While b P0), Normal s') # zs = (Q, t) # cfg1"
    using CptnModNestWhile2.prems by fastforce
  then show ?case
    using CptnModNestWhile2.hyps(1) CptnModNestWhile2.hyps(3) 
          CptnModNestWhile2.hyps(5) CptnModNestWhile2.hyps(6) 
          cptn_mod_nest_call.CptnModNestSeq2 by blast
next
  case (CptnModNestWhile3 n \<Gamma> P0 s' xs b zs) thus ?case
    by (metis (no_types) CptnModNestWhile3.hyps(1) CptnModNestWhile3.hyps(3) CptnModNestWhile3.hyps(5) 
                         CptnModNestWhile3.hyps(6) CptnModNestWhile3.hyps(8) CptnModNestWhile3.prems 
                         cptn_mod_nest_call.CptnModNestSeq3 list.inject)  
qed (fastforce+) 




definition min_call where
"min_call n \<Gamma> cfs \<equiv> (n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call \<and> (\<forall>m<n. \<not>((m,\<Gamma>,cfs) \<in>  cptn_mod_nest_call))"

lemma minimum_nest_call:
  "(m,\<Gamma>,cfs) \<in> cptn_mod_nest_call \<Longrightarrow>
   \<exists>n. min_call n \<Gamma> cfs"
unfolding min_call_def
proof (induct arbitrary: m rule:cptn_mod_nest_call.induct) 
 case (CptnModNestOne) thus ?case using cptn_mod_nest_call.CptnModNestOne by blast 
next
  case (CptnModNestEnv \<Gamma> P s t n xs) 
  then have "\<not> \<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow> (P, t)" 
   using mod_env_not_component step_change_p_or_eq_s by blast 
  then obtain min_n where min:"(min_n, \<Gamma>, (P, t) # xs) \<in> cptn_mod_nest_call \<and> 
                             (\<forall>m<min_n.  (m, \<Gamma>, (P, t) # xs) \<notin> cptn_mod_nest_call)" 
    using CptnModNestEnv by blast
  then have  "(min_n, \<Gamma>, (P,s)#(P, t) # xs) \<in> cptn_mod_nest_call"     
    using cptn_mod_nest_call.CptnModNestEnv CptnModNestEnv by blast
  also have "(\<forall>m<min_n. (m, \<Gamma>, (P, s)#(P, t) # xs) \<notin> cptn_mod_nest_call)"
    using elim_cptn_mod_nest_call_n min by fastforce    
  ultimately show ?case by auto  
next
  case (CptnModNestSkip \<Gamma> P s t n xs)    
  then obtain min_n where 
     min:"(min_n, \<Gamma>, (LanguageCon.com.Skip, t) # xs) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_n. (m, \<Gamma>, (LanguageCon.com.Skip, t) # xs) \<notin> cptn_mod_nest_call)" 
    by auto
  then have "(min_n, \<Gamma>, (P,s)#(LanguageCon.com.Skip, t) # xs) \<in> cptn_mod_nest_call"
    using cptn_mod_nest_call.CptnModNestSkip CptnModNestSkip by blast
  also have "(\<forall>m<min_n. (m, \<Gamma>, (P, s)#(LanguageCon.com.Skip, t) # xs) \<notin> cptn_mod_nest_call)"
    using elim_cptn_mod_nest_call_n min by blast      
  ultimately show ?case by fastforce   
next
   case (CptnModNestThrow \<Gamma> P s t n xs) thus ?case
     by (meson cptn_mod_nest_call.CptnModNestThrow elim_cptn_mod_nest_call_n)    
next
  case (CptnModNestCondT n \<Gamma> P0 s xs b P1) thus ?case
    by (meson cptn_mod_nest_call.CptnModNestCondT elim_cptn_mod_nest_call_n)
next
  case (CptnModNestCondF n \<Gamma> P1 s xs b P0) thus ?case
    by (meson cptn_mod_nest_call.CptnModNestCondF elim_cptn_mod_nest_call_n)
next
  case (CptnModNestSeq1 n \<Gamma> P s xs zs Q) thus ?case
    by (metis (no_types, lifting) Seq_P_Not_finish cptn_mod_nest_call.CptnModNestSeq1 div_seq_nest)
next
  case (CptnModNestSeq2 n \<Gamma> P s xs Q ys zs) 
  then obtain min_p where 
     min_p:"(min_p, \<Gamma>, (P,  s) # xs) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_p. (m, \<Gamma>, (P, s) # xs) \<notin> cptn_mod_nest_call)" 
    by auto 
  from CptnModNestSeq2(5) obtain min_q where
    min_q:"(min_q, \<Gamma>, (Q, snd (last ((P, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_q. (m, \<Gamma>, (Q, snd (last ((P, s) # xs))) # ys) \<notin> cptn_mod_nest_call)"
  by auto
  thus ?case
  proof(cases "min_p\<ge>min_q")
    case True
    then have "(min_p, \<Gamma>, (Q, snd (last ((P,s) # xs))) # ys) \<in> cptn_mod_nest_call"
      using min_q using cptn_mod_nest_mono by blast 
    then have "(min_p, \<Gamma>, (Seq P Q, s) # zs) \<in> cptn_mod_nest_call"
      using conjunct1[OF min_p] cptn_mod_nest_call.CptnModNestSeq2[of min_p \<Gamma> P s xs Q ys zs] 
            CptnModNestSeq2(6)  CptnModNestSeq2(3)
    by blast
    also have "\<forall>m<min_p. (m, \<Gamma>,(Seq P Q,s) # zs) \<notin> cptn_mod_nest_call"
      by (metis CptnModNestSeq2.hyps(3) CptnModNestSeq2.hyps(6) Seq_P_Ends_Normal div_seq_nest min_p)      
    ultimately show ?thesis by auto
  next
    case False 
    then have "(min_q, \<Gamma>, (P,  s) # xs) \<in> cptn_mod_nest_call"
      using min_p cptn_mod_nest_mono by force 
    then have "(min_q, \<Gamma>, (Seq P Q, s) # zs) \<in> cptn_mod_nest_call"
      using conjunct1[OF min_q] cptn_mod_nest_call.CptnModNestSeq2[of min_q \<Gamma> P s xs Q ys zs] 
            CptnModNestSeq2(6)  CptnModNestSeq2(3)
    by blast
    also have "\<forall>m<min_q. (m, \<Gamma>,(Seq P Q,s) # zs) \<notin> cptn_mod_nest_call"
     proof -
      {fix m
      assume min_m:"m<min_q"
      then have "(m, \<Gamma>,(Seq P Q, s) # zs) \<notin> cptn_mod_nest_call"
      proof -
      {assume ass:"(m, \<Gamma>, (Seq P Q, s) # zs) \<in> cptn_mod_nest_call"
       then obtain xs' s' s'' where 
          m_cptn:"(m, \<Gamma>, (P, s) # xs') \<in> cptn_mod_nest_call \<and> 
                   seq_cond_nest zs Q xs' P s s'' s' \<Gamma> m" 
         using  
          div_seq_nest[of m \<Gamma> "(LanguageCon.com.Seq P Q, s) # zs"]
          by fastforce
       then have "seq_cond_nest zs Q xs' P s s'' s' \<Gamma> m" by auto
       then have ?thesis
         using Seq_P_Ends_Normal[OF CptnModNestSeq2(6) CptnModNestSeq2(3) ass]
               min_m min_q 
         by (metis last_length)          
      } thus ?thesis by auto
      qed
      }thus ?thesis by auto
    qed  
    ultimately show ?thesis by auto
  qed
next
  case (CptnModNestSeq3 n \<Gamma> P s xs s' ys zs Q) 
  then obtain min_p where 
     min_p:"(min_p, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_p. (m, \<Gamma>, (P, Normal s) # xs) \<notin> cptn_mod_nest_call)" 
    by auto 
  from CptnModNestSeq3(6) obtain min_q where
    min_q:"(min_q, \<Gamma>, (Throw, Normal s') # ys) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_q. (m, \<Gamma>, (Throw, Normal s') # ys) \<notin> cptn_mod_nest_call)"
  by auto
  thus ?case
  proof(cases "min_p\<ge>min_q")
    case True 
    then have "(min_p, \<Gamma>, (Throw, Normal s') # ys) \<in> cptn_mod_nest_call"
      using min_q using cptn_mod_nest_mono by blast 
    then have "(min_p, \<Gamma>, (Seq P Q, Normal s) # zs) \<in> cptn_mod_nest_call"
      using conjunct1[OF min_p] cptn_mod_nest_call.CptnModNestSeq3[of min_p \<Gamma> P s xs s' ys zs Q] 
            CptnModNestSeq3(4)  CptnModNestSeq3(3) CptnModNestSeq3(7)
    by blast
    also have "\<forall>m<min_p. (m, \<Gamma>,(Seq P Q,Normal s) # zs) \<notin> cptn_mod_nest_call"
      by (metis CptnModNestSeq3.hyps(3) CptnModNestSeq3.hyps(4) CptnModNestSeq3.hyps(7) Seq_P_Ends_Abort div_seq_nest min_p)
    ultimately show ?thesis by auto
  next
    case False
    then have "(min_q, \<Gamma>, (P,  Normal s) # xs) \<in> cptn_mod_nest_call"
      using min_p cptn_mod_nest_mono by force 
    then have "(min_q, \<Gamma>, (Seq P Q, Normal s) # zs) \<in> cptn_mod_nest_call"
      using conjunct1[OF min_q] cptn_mod_nest_call.CptnModNestSeq3[of min_q \<Gamma> P s xs s' ys zs Q] 
            CptnModNestSeq3(4)  CptnModNestSeq3(3) CptnModNestSeq3(7)
    by blast
    also have "\<forall>m<min_q. (m, \<Gamma>,(Seq P Q,Normal s) # zs) \<notin> cptn_mod_nest_call"
      by (metis CptnModNestSeq3.hyps(3) CptnModNestSeq3.hyps(4) CptnModNestSeq3.hyps(7) Seq_P_Ends_Abort div_seq_nest min_q)     
    ultimately show ?thesis by auto
  qed 
next
  case (CptnModNestWhile1 n \<Gamma> P s xs b zs) 
  then obtain min_n where 
     min:"(min_n, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_n. (m, \<Gamma>, (P, Normal s) # xs) \<notin> cptn_mod_nest_call)" 
    by auto
  then have "(min_n, \<Gamma>, (While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<in> cptn_mod_nest_call"
    using cptn_mod_nest_call.CptnModNestWhile1[of min_n \<Gamma> P s xs b zs] CptnModNestWhile1
    by meson 
  also have "\<forall>m<min_n. (m, \<Gamma>,(While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<notin> cptn_mod_nest_call"
    by (metis CptnModNestWhile1.hyps(4) Seq_P_Not_finish div_seq_nest elim_cptn_mod_nest_call_n min) 
  ultimately show ?case by auto
next
  case (CptnModNestWhile2 n \<Gamma> P s xs b zs ys) 
  then obtain min_n_p where 
     min_p:"(min_n_p, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_n_p. (m, \<Gamma>, (P, Normal s) # xs) \<notin> cptn_mod_nest_call)" 
    by auto
  from CptnModNestWhile2 obtain min_n_w where
     min_w:"(min_n_w, \<Gamma>, (LanguageCon.com.While b P, snd (last ((P, Normal s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_n_w. (m, \<Gamma>, (LanguageCon.com.While b P, snd (last ((P, Normal s) # xs))) # ys)
               \<notin> cptn_mod_nest_call)"
    by auto
  thus ?case 
  proof (cases "min_n_p\<ge>min_n_w")
    case True 
    then have "(min_n_p, \<Gamma>, 
      (LanguageCon.com.While b P, snd (last ((P, Normal s) # xs))) # ys) \<in> cptn_mod_nest_call"
      using min_w using cptn_mod_nest_mono by blast 
    then have "(min_n_p, \<Gamma>, (While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<in> cptn_mod_nest_call"
      using min_p cptn_mod_nest_call.CptnModNestWhile2[of min_n_p \<Gamma> P s xs b zs] CptnModNestWhile2
      by blast
    also have "\<forall>m<min_n_p. (m, \<Gamma>,(While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<notin> cptn_mod_nest_call"
      by (metis CptnModNestWhile2.hyps(3) CptnModNestWhile2.hyps(5) 
                Seq_P_Ends_Normal div_seq_nest elim_cptn_mod_nest_call_n min_p)    
    ultimately show ?thesis by auto  
  next
    case False
    then have False:"min_n_p<min_n_w" by auto
    then have "(min_n_w, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call"
      using min_p  cptn_mod_nest_mono by force 
    then have "(min_n_w, \<Gamma>, (While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<in> cptn_mod_nest_call"
      using min_w min_p cptn_mod_nest_call.CptnModNestWhile2[of min_n_w \<Gamma> P s xs b zs] CptnModNestWhile2
      by blast
    also have "\<forall>m<min_n_w. (m, \<Gamma>,(While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<notin> cptn_mod_nest_call"      
    proof -
      {fix m
      assume min_m:"m<min_n_w"
      then have "(m, \<Gamma>,(While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<notin> cptn_mod_nest_call"
      proof -
      {assume "(m, \<Gamma>,(While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<in> cptn_mod_nest_call"
       then have a1:"(m, \<Gamma>,(Seq P (While b P), Normal s) # zs) \<in> cptn_mod_nest_call"      
         using elim_cptn_mod_nest_not_env_call by fastforce
       then obtain xs' s' s'' where 
          m_cptn:"(m, \<Gamma>, (P, Normal s) # xs') \<in> cptn_mod_nest_call  \<and> 
                   seq_cond_nest zs (While b P) xs' P (Normal s) s'' s' \<Gamma> m" 
         using  
          div_seq_nest[of m \<Gamma> "(LanguageCon.com.Seq P (LanguageCon.com.While b P), Normal s) # zs"]
          by fastforce
       then have "seq_cond_nest zs (While b P) xs' P (Normal s) s'' s' \<Gamma> m" by auto
       then have ?thesis unfolding seq_cond_nest_def
         by (metis CptnModNestWhile2.hyps(3) CptnModNestWhile2.hyps(5) Seq_P_Ends_Normal a1 last_length m_cptn min_m min_w)           
     } thus ?thesis by auto
     qed
     }thus ?thesis by auto
    qed
    ultimately show ?thesis by auto
  qed
next
  case (CptnModNestWhile3 n \<Gamma> P s xs b s' ys zs) 
  then obtain min_n_p where 
     min_p:"(min_n_p, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_n_p. (m, \<Gamma>, (P, Normal s) # xs) \<notin> cptn_mod_nest_call)" 
    by auto
  from CptnModNestWhile3 obtain min_n_w where
     min_w:"(min_n_w, \<Gamma>, (Throw, snd (last ((P, Normal s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_n_w. (m, \<Gamma>, (Throw, snd (last ((P, Normal s) # xs))) # ys)
               \<notin> cptn_mod_nest_call)"
    by auto
  thus ?case 
  proof (cases "min_n_p\<ge>min_n_w")
    case True 
    then have "(min_n_p, \<Gamma>, 
      (Throw, snd (last ((P, Normal s) # xs))) # ys) \<in> cptn_mod_nest_call"
      using min_w using cptn_mod_nest_mono by blast 
    then have "(min_n_p, \<Gamma>, (While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<in> cptn_mod_nest_call"
      using min_p cptn_mod_nest_call.CptnModNestWhile3[of min_n_p \<Gamma> P s xs b s' ys zs] 
            CptnModNestWhile3
      by fastforce
    also have "\<forall>m<min_n_p. (m, \<Gamma>,(While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<notin> cptn_mod_nest_call"
      by (metis CptnModNestWhile3.hyps(3) CptnModNestWhile3.hyps(5) CptnModNestWhile3.hyps(8) 
            Seq_P_Ends_Abort div_seq_nest elim_cptn_mod_nest_call_n min_p)    
    ultimately show ?thesis by auto  
  next
    case False
    then have False:"min_n_p<min_n_w" by auto
    then have "(min_n_w, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call"
      using min_p  cptn_mod_nest_mono by force 
    then have "(min_n_w, \<Gamma>, (While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<in> cptn_mod_nest_call"
      using min_w min_p cptn_mod_nest_call.CptnModNestWhile3[of min_n_w \<Gamma> P s xs b s' ys zs] 
            CptnModNestWhile3
      by fastforce      
    also have "\<forall>m<min_n_w. (m, \<Gamma>,(While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<notin> cptn_mod_nest_call"
    proof -
      {fix m
      assume min_m:"m<min_n_w"
      then have "(m, \<Gamma>,(While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<notin> cptn_mod_nest_call"
      proof -
      {assume "(m, \<Gamma>,(While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<in> cptn_mod_nest_call"
       then have s1:"(m, \<Gamma>,(Seq P (While b P), Normal s) # zs) \<in> cptn_mod_nest_call"      
         using elim_cptn_mod_nest_not_env_call by fastforce
       then obtain xs' s' s'' where 
          m_cptn:"(m, \<Gamma>, (P, Normal s) # xs') \<in> cptn_mod_nest_call  \<and> 
                   seq_cond_nest zs (While b P) xs' P (Normal s) s'' s' \<Gamma> m" 
         using  
          div_seq_nest[of m \<Gamma> "(LanguageCon.com.Seq P (LanguageCon.com.While b P), Normal s) # zs"]
          by fastforce
       then have "seq_cond_nest zs (While b P) xs' P (Normal s) s'' s' \<Gamma> m" by auto
       then have ?thesis unfolding seq_cond_nest_def
         by (metis CptnModNestWhile3.hyps(3) CptnModNestWhile3.hyps(5) CptnModNestWhile3.hyps(8) Seq_P_Ends_Abort s1 m_cptn min_m min_w)       
     } thus ?thesis by auto
     qed
     }thus ?thesis by auto
    qed
    ultimately show ?thesis by auto
  qed
next
  case (CptnModNestCall n \<Gamma> bdy s xs f) thus ?case
  proof -
    { fix nn :: "nat \<Rightarrow> nat"
     obtain nna :: nat where
      ff1: "(nna, \<Gamma>, (bdy, Normal s) # xs) \<in> cptn_mod_nest_call \<and> (\<forall>n. \<not> n < nna \<or> (n, \<Gamma>, (bdy, Normal s) # xs) \<notin> cptn_mod_nest_call)"
      by (meson CptnModNestCall.hyps(2))
    moreover
    { assume "(nn (nn (Suc nna)), \<Gamma>, (bdy, Normal s) # xs) \<in> cptn_mod_nest_call"
      then have "\<not> Suc (nn (nn (Suc nna))) < Suc nna"
        using ff1 by blast
      then have "(nn (Suc nna), \<Gamma>, (LanguageCon.com.Call f, Normal s) # (bdy, Normal s) # xs) \<in> cptn_mod_nest_call \<longrightarrow> (\<exists>n. (n, \<Gamma>, (LanguageCon.com.Call f, Normal s) # (bdy, Normal s) # xs) \<in> cptn_mod_nest_call \<and> 
                (\<not> nn n < n \<or> (nn n, \<Gamma>, (LanguageCon.com.Call f, Normal s) # (bdy, Normal s) # xs) \<notin> cptn_mod_nest_call))"
        using ff1 by (meson CptnModNestCall.hyps(3) CptnModNestCall.hyps(4) cptn_mod_nest_call.CptnModNestCall less_trans_Suc) }
    ultimately have "\<exists>n. (n, \<Gamma>, (LanguageCon.com.Call f, Normal s) # (bdy, Normal s) # xs) \<in> cptn_mod_nest_call \<and> (\<not> nn n < n \<or> (nn n, \<Gamma>, (LanguageCon.com.Call f, Normal s) # (bdy, Normal s) # xs) \<notin> cptn_mod_nest_call)"
      by (metis (no_types) CptnModNestCall.hyps(3) CptnModNestCall.hyps(4) cptn_mod_nest_call.CptnModNestCall elim_cptn_mod_nest_call_n) }
   then show ?thesis
     by meson
  qed     
next 
 case (CptnModNestDynCom n \<Gamma> c s xs) thus ?case
   by (meson cptn_mod_nest_call.CptnModNestDynCom elim_cptn_mod_nest_call_n)
next
  case (CptnModNestGuard n \<Gamma> c s xs g f) thus ?case 
    by (meson cptn_mod_nest_call.CptnModNestGuard elim_cptn_mod_nest_call_n)   
next
 case (CptnModNestCatch1 n \<Gamma> P s xs  zs Q) thus ?case
   by (metis (no_types, lifting) Catch_P_Not_finish cptn_mod_nest_call.CptnModNestCatch1 div_catch_nest)
next
 case (CptnModNestCatch2 n \<Gamma> P s xs ys zs Q) 
 then obtain min_p where 
     min_p:"(min_p, \<Gamma>, (P,  s) # xs) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_p. (m, \<Gamma>, (P, s) # xs) \<notin> cptn_mod_nest_call)" 
    by auto 
  from CptnModNestCatch2(5) obtain min_q where
    min_q:"(min_q, \<Gamma>, (Skip, snd (last ((P, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_q. (m, \<Gamma>, (Skip, snd (last ((P, s) # xs))) # ys) \<notin> cptn_mod_nest_call)"
  by auto
  thus ?case
  proof(cases "min_p\<ge>min_q")
    case True
    then have "(min_p, \<Gamma>, (Skip, snd (last ((P,s) # xs))) # ys) \<in> cptn_mod_nest_call"
      using min_q using cptn_mod_nest_mono by blast 
    then have "(min_p, \<Gamma>, (Catch P Q, s) # zs) \<in> cptn_mod_nest_call"
      using conjunct1[OF min_p] cptn_mod_nest_call.CptnModNestCatch2[of min_p \<Gamma> P s xs] 
            CptnModNestCatch2(6)  CptnModNestCatch2(3)
    by blast
    also have "\<forall>m<min_p. (m, \<Gamma>,(Catch P Q,s) # zs) \<notin> cptn_mod_nest_call"
     proof -
      {fix m
      assume min_m:"m<min_p"
      then have "(m, \<Gamma>,(Catch P Q, s) # zs) \<notin> cptn_mod_nest_call"
      proof -
      {assume ass:"(m, \<Gamma>, (Catch P Q, s) # zs) \<in> cptn_mod_nest_call"
       then obtain xs' s' s'' where 
          m_cptn:"(m, \<Gamma>, (P, s) # xs') \<in> cptn_mod_nest_call \<and> 
                   catch_cond_nest zs Q xs' P s s'' s' \<Gamma> m" 
         using  
          div_catch_nest[of m \<Gamma> "(Catch P Q, s) # zs"]
          by fastforce
       then have "catch_cond_nest zs Q xs' P s s'' s' \<Gamma> m" by auto
       then have "xs=xs'" 
         using Catch_P_Ends_Skip[OF CptnModNestCatch2(6) CptnModNestCatch2(3)]   
         by fastforce
       then have "(m, \<Gamma>, (P,s) # xs) \<in> cptn_mod_nest_call"
         using m_cptn by auto
       then have False using min_p min_m by fastforce
    } thus ?thesis by auto
    qed
    }thus ?thesis by auto
  qed
  ultimately show ?thesis by auto
  next
    case False
    then have "(min_q, \<Gamma>, (P,  s) # xs) \<in> cptn_mod_nest_call"
      using min_p cptn_mod_nest_mono by force 
    then have "(min_q, \<Gamma>, (Catch P Q, s) # zs) \<in> cptn_mod_nest_call"
      using conjunct1[OF min_q] cptn_mod_nest_call.CptnModNestCatch2[of min_q \<Gamma> P s xs ] 
            CptnModNestCatch2(6)  CptnModNestCatch2(3)
    by blast
    also have "\<forall>m<min_q. (m, \<Gamma>,(Catch P Q,s) # zs) \<notin> cptn_mod_nest_call"
     proof -
      {fix m
      assume min_m:"m<min_q"
      then have "(m, \<Gamma>,(Catch P Q, s) # zs) \<notin> cptn_mod_nest_call"
      proof -
      {assume ass:"(m, \<Gamma>, (Catch P Q, s) # zs) \<in> cptn_mod_nest_call"
       then obtain xs' s' s'' where 
          m_cptn:"(m, \<Gamma>, (P, s) # xs') \<in> cptn_mod_nest_call \<and> 
                   catch_cond_nest zs Q xs' P s s'' s' \<Gamma> m" 
         using  
          div_catch_nest[of m \<Gamma> "(Catch P Q, s) # zs"]
          by fastforce
       then have "catch_cond_nest zs Q xs' P s s'' s' \<Gamma> m" by auto
       then have ?thesis
         using Catch_P_Ends_Skip[OF CptnModNestCatch2(6) CptnModNestCatch2(3)]
               min_m min_q 
       by blast         
      } thus ?thesis by auto
      qed
      }thus ?thesis by auto
    qed  
    ultimately show ?thesis by auto
  qed
next
 case (CptnModNestCatch3 n \<Gamma> P s xs s' Q ys zs ) then obtain min_p where 
     min_p:"(min_p, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_p. (m, \<Gamma>, (P, Normal s) # xs) \<notin> cptn_mod_nest_call)" 
    by auto 
  from CptnModNestCatch3(6)  CptnModNestCatch3(4) obtain min_q where
    min_q:"(min_q, \<Gamma>, (Q,  snd (last ((P, Normal s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_q. (m, \<Gamma>, (Q,  snd (last ((P, Normal s) # xs))) # ys) \<notin> cptn_mod_nest_call)"
  by auto
  thus ?case
  proof(cases "min_p\<ge>min_q")
    case True
    then have "(min_p, \<Gamma>, (Q,  snd (last ((P, Normal s) # xs))) # ys) \<in> cptn_mod_nest_call"
      using min_q using cptn_mod_nest_mono by blast 
    then have "(min_p, \<Gamma>, (Catch P Q, Normal s) # zs) \<in> cptn_mod_nest_call"
      using conjunct1[OF min_p] cptn_mod_nest_call.CptnModNestCatch3[of min_p \<Gamma> P s xs s' Q ys zs] 
            CptnModNestCatch3(4)  CptnModNestCatch3(3) CptnModNestCatch3(7)
    by fastforce
    also have "\<forall>m<min_p. (m, \<Gamma>,(Catch P Q,Normal s) # zs) \<notin> cptn_mod_nest_call"
     proof -
      {fix m
      assume min_m:"m<min_p"
      then have "(m, \<Gamma>,(Catch P Q, Normal s) # zs) \<notin> cptn_mod_nest_call"
      proof -
      {assume ass:"(m, \<Gamma>, (Catch P Q,Normal s) # zs) \<in> cptn_mod_nest_call"
       then obtain xs' ns' ns'' where 
          m_cptn:"(m, \<Gamma>, (P, Normal s) # xs') \<in> cptn_mod_nest_call \<and> 
                   catch_cond_nest zs Q xs' P (Normal s) ns'' ns' \<Gamma> m" 
         using  
          div_catch_nest[of m \<Gamma> "(Catch P Q, Normal s) # zs"]
          by fastforce
       then have "catch_cond_nest zs Q xs' P (Normal s) ns'' ns' \<Gamma> m" by auto       
       then have "xs=xs'" 
         using  Catch_P_Ends_Normal[OF CptnModNestCatch3(7)  CptnModNestCatch3(3) CptnModNestCatch3(4)]   
         by fastforce
       then have "(m, \<Gamma>, (P,Normal s) # xs) \<in> cptn_mod_nest_call"
         using m_cptn by auto
       then have False using min_p min_m by fastforce
    } thus ?thesis by auto
    qed
    }thus ?thesis by auto
  qed
  ultimately show ?thesis by auto
  next
    case False
    then have "(min_q, \<Gamma>, (P,  Normal s) # xs) \<in> cptn_mod_nest_call"
      using min_p cptn_mod_nest_mono by force 
    then have "(min_q, \<Gamma>, (Catch P Q, Normal s) # zs) \<in> cptn_mod_nest_call"
      using conjunct1[OF min_q] cptn_mod_nest_call.CptnModNestCatch3[of min_q \<Gamma> P s xs s' ] 
            CptnModNestCatch3(4)  CptnModNestCatch3(3) CptnModNestCatch3(7)
    by blast
    also have "\<forall>m<min_q. (m, \<Gamma>,(Catch P Q,Normal s) # zs) \<notin> cptn_mod_nest_call"
     proof -
      {fix m
      assume min_m:"m<min_q"
      then have "(m, \<Gamma>,(Catch P Q, Normal s) # zs) \<notin> cptn_mod_nest_call"
      proof -
      {assume ass:"(m, \<Gamma>, (Catch P Q, Normal s) # zs) \<in> cptn_mod_nest_call"
       then obtain xs' ns' ns'' where 
          m_cptn:"(m, \<Gamma>, (P, Normal s) # xs') \<in> cptn_mod_nest_call \<and> 
                   catch_cond_nest zs Q xs' P (Normal s) ns'' ns' \<Gamma> m" 
         using  
          div_catch_nest[of m \<Gamma> "(Catch P Q, Normal s) # zs"]
          by fastforce
       then have "catch_cond_nest zs Q xs' P (Normal s) ns'' ns' \<Gamma> m" by auto
       then have ?thesis
         using Catch_P_Ends_Normal[OF CptnModNestCatch3(7) CptnModNestCatch3(3)  CptnModNestCatch3(4)]
               min_m min_q 
         by (metis last_length)                                
      } thus ?thesis by auto
      qed
      }thus ?thesis by auto
    qed  
    ultimately show ?thesis by auto
  qed  
qed

  lemma elim_cptn_mod_min_nest_call:
 assumes a0:"min_call n \<Gamma> cfg" and
         a1:"cfg = (P,s)#(Q,t)#cfg1" and
         a2:"(\<forall>f. redex P \<noteq> Call f) \<or>  
             SmallStepCon.redex P = LanguageCon.com.Call fn \<and> \<Gamma> fn = None \<or>
            (redex P = Call fn \<and> (\<forall>sa. s\<noteq>Normal sa)) \<or>
            (redex P = Call fn \<and> P=Q)"     
 shows "min_call n \<Gamma> ((Q,t)#cfg1)"
proof -
  have a0: "(n,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" and
       a0': "(\<forall>m<n. (m, \<Gamma>, cfg) \<notin> cptn_mod_nest_call)"
  using a0 unfolding min_call_def by auto
  then have "(n,\<Gamma>,(Q,t)#cfg1) \<in>  cptn_mod_nest_call"  
    using a0 a1 elim_cptn_mod_nest_call_n by blast
  also have "(\<forall>m<n. (m, \<Gamma>, (Q,t)#cfg1) \<notin> cptn_mod_nest_call)"      
  proof-
  { assume "\<not>(\<forall>m<n. (m, \<Gamma>, (Q,t)#cfg1) \<notin> cptn_mod_nest_call)"
    then obtain m where 
      asm0:"m<n" and 
      asm1:"(m, \<Gamma>, (Q,t)#cfg1) \<in> cptn_mod_nest_call"
    by auto
    then have "(m, \<Gamma>, cfg) \<in> cptn_mod_nest_call" 
      using  a0 a1 a2  cptn_mod_nest_cptn_mod cptn_if_cptn_mod cptn_mod_nest_call.CptnModNestEnv
          cptn_elim_cases(2)  not_func_redex_cptn_mod_nest_n'          
      by (metis (no_types, lifting) mod_env_not_component)

    then have False using a0' asm0 by auto
  } thus ?thesis by auto qed
  ultimately show ?thesis unfolding min_call_def by auto
qed

  

lemma elim_call_cptn_mod_min_nest_call:
 assumes a0:"min_call n \<Gamma> cfg" and
         a1:"cfg = (P,s)#(Q,t)#cfg1" and
         a2:"P = Call f \<and>  
             \<Gamma> f = Some Q \<and> (\<exists>sa. s=Normal sa) \<and> P\<noteq>Q"          
 shows "min_call (n-1) \<Gamma> ((Q,t)#cfg1)"
proof -
  obtain s' where a0: "(n,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" and
       a0': "(\<forall>m<n. (m, \<Gamma>, cfg) \<notin> cptn_mod_nest_call)" and
       a2': "s= Normal s'" 
    using a0 a2 unfolding min_call_def by auto  
  then have "(n-1,\<Gamma>,(Q,t)#cfg1) \<in>  cptn_mod_nest_call" 
    using a1 a2 a2' elim_cptn_mod_nest_call_n_dec[of n \<Gamma> f s' cfg1 Q]
    by (metis (no_types, lifting) SmallStepCon.redex.simps(7) call_f_step_not_s_eq_t_false 
         cptn_elim_cases(2) cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod option.sel)   
  thus ?thesis
  proof -
    obtain nn :: "(('b, 'a, 'c, 'd) LanguageCon.com \<times> ('b, 'c) xstate) list \<Rightarrow> 
                  ('a \<Rightarrow> ('b, 'a, 'c, 'd) LanguageCon.com option) \<Rightarrow> nat \<Rightarrow> nat" where
      "\<forall>x0 x1 x2. (\<exists>v3<x2. (v3, x1, x0) \<in> cptn_mod_nest_call) = 
                  (nn x0 x1 x2 < x2 \<and> (nn x0 x1 x2, x1, x0) \<in> cptn_mod_nest_call)"
      by moura
    then have f1: "\<forall>n f ps. (\<not> min_call n f ps \<or> (n, f, ps) \<in> cptn_mod_nest_call \<and> 
                            (\<forall>na. \<not> na < n \<or> (na, f, ps) \<notin> cptn_mod_nest_call)) \<and> 
                            (min_call n f ps \<or> (n, f, ps) \<notin> cptn_mod_nest_call \<or> 
                    nn ps f n < n \<and> (nn ps f n, f, ps) \<in> cptn_mod_nest_call)"
      by (meson min_call_def)
    then have f2: "(n, \<Gamma>, (P, s) # (Q, t) # cfg1) \<in> cptn_mod_nest_call \<and> 
                   (\<forall>na. \<not> na < n \<or> (na, \<Gamma>, (P, s) # (Q, t) # cfg1) \<notin> cptn_mod_nest_call)"
      using a1 assms(1) by blast
    obtain bb :: 'b where
      f3: "s = Normal bb"
      using a2 by blast
    then have f4: "(LanguageCon.com.Call f, Normal bb) = (P, s)"
      using a2 by blast
    have f5: "n - 1 < n"
      using f2 by (metis (no_types) Suc_diff_Suc a2 diff_Suc_eq_diff_pred elim_cptn_mod_nest_call_n_greater_zero lessI minus_nat.diff_0)
    have f6: "(LanguageCon.com.Call f, Normal bb) = (P, s)"
      using f3 a2 by blast
    have f7: "Normal bb = t"
      using f4 f2 by (metis (no_types) SmallStepCon.redex.simps(7) a2 
                            call_f_step_not_s_eq_t_false cptn_elim_cases(2) 
                            cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod)
    have "(nn ((Q, t) # cfg1) \<Gamma> (n - 1), \<Gamma>, (Q, Normal bb) # cfg1) \<in> cptn_mod_nest_call \<longrightarrow> 
              (Suc (nn ((Q, t) # cfg1) \<Gamma> (n - 1)), \<Gamma>, 
            (LanguageCon.com.Call f, Normal bb) # (Q, Normal bb) # cfg1) \<in> cptn_mod_nest_call"
      using a2 cptn_mod_nest_call.CptnModNestCall by fastforce
    then show ?thesis
      using f7 f6 f5 f2 f1 \<open>(n - 1, \<Gamma>, (Q, t) # cfg1) \<in> cptn_mod_nest_call\<close> less_trans_Suc by blast
  qed  
  
qed

lemma redex_not_call_seq_catch:
 assumes a0:"redex P = Call f \<and> P\<noteq>Call f"          
 shows "\<exists>p1 p2. P = Seq p1 p2 \<or> P = Catch p1 p2"
using a0 unfolding min_call_def
proof(induct P)
qed(fastforce+)

lemma skip_all_skip:
  assumes a0:"(\<Gamma>,cfg)\<in>cptn" and
          a1:"cfg = (Skip,s)#cfg1"
  shows "\<forall>i<length cfg. fst(cfg!i) = Skip"
using a0 a1
proof(induct cfg1 arbitrary:cfg s)
  case Nil thus ?case by auto
next
  case (Cons x xs)
  then obtain s' where x:"x = (Skip,s')"
    by (metis CptnMod_elim_cases(1) cptn_eq_cptn_mod_set  stepc_elim_cases(1))
  moreover have cptn:"(\<Gamma>,x#xs)\<in>cptn"
    using Cons.prems(1) Cons.prems(2) cptn_dest_pair by blast
  moreover have 
    xs:"x # xs = (LanguageCon.com.Skip, s') # xs" using x by auto
  ultimately show ?case using Cons(1)[OF cptn xs] Cons(3)
    using diff_Suc_1 fstI length_Cons less_Suc_eq_0_disj nth_Cons' by auto 
qed

lemma skip_all_skip_throw:
  assumes a0:"(\<Gamma>,cfg)\<in>cptn" and
          a1:"cfg = (Throw,s)#cfg1"
  shows "\<forall>i<length cfg. fst(cfg!i) = Skip \<or> fst(cfg!i) = Throw"
using a0 a1
proof(induct cfg1 arbitrary:cfg s)
  case Nil thus ?case by auto
next
  case (Cons x xs)
  then obtain s' where x:"x = (Skip,s') \<or> x = (Throw, s')"
    by (metis CptnMod_elim_cases(10) cptn_eq_cptn_mod_set)    
  then have cptn:"(\<Gamma>,x#xs)\<in>cptn"
    using Cons.prems(1) Cons.prems(2) cptn_dest_pair by blast
  show ?case using x
  proof 
    assume "x=(Skip,s')" thus ?thesis using skip_all_skip Cons(3)
      using cptn fstI length_Cons less_Suc_eq_0_disj nth_Cons' nth_Cons_Suc skip_all_skip 
      by fastforce 
  next
    assume x:"x=(Throw,s')"
    moreover have cptn:"(\<Gamma>,x#xs)\<in>cptn"
      using Cons.prems(1) Cons.prems(2) cptn_dest_pair by blast
    moreover have 
      xs:"x # xs = (LanguageCon.com.Throw, s') # xs" using x by auto
    ultimately show ?case using Cons(1)[OF cptn xs] Cons(3)
    using diff_Suc_1 fstI length_Cons less_Suc_eq_0_disj nth_Cons' by auto 
  qed  
qed

  
lemma skip_min_nested_call_0:
  assumes a0:"min_call n \<Gamma> cfg" and
          a1:"cfg = (Skip,s)#cfg1"
  shows "n=0"
proof -
  have asm0:"(n, \<Gamma>, cfg) \<in> cptn_mod_nest_call" and 
       asm1:"(\<forall>m<n. (m, \<Gamma>, cfg) \<notin> cptn_mod_nest_call)"  
       using a0 unfolding min_call_def by auto  
  show ?thesis using a1 asm0 asm1
  proof (induct cfg1 arbitrary: cfg s n)
    case Nil thus ?case
      using cptn_mod_nest_call.CptnModNestOne neq0_conv by blast
  next
    case (Cons x xs)
      then obtain Q s' where cfg:"cfg = (LanguageCon.com.Skip, s) # (Q,s') # xs" by force
      then have min_call:"min_call n \<Gamma> cfg" using Cons unfolding min_call_def by auto
      then have "(\<forall>f. SmallStepCon.redex Skip \<noteq> LanguageCon.com.Call f)" by auto
      then have "min_call n \<Gamma> ((Q, s')#xs)" 
        using elim_cptn_mod_min_nest_call[OF min_call cfg] cfg
        by simp
      thus ?case using Cons cfg unfolding min_call_def
      proof -
        assume a1: "(n, \<Gamma>, (Q, s') # xs) \<in> cptn_mod_nest_call \<and> (\<forall>m<n. (m, \<Gamma>, (Q, s') # xs) \<notin> cptn_mod_nest_call)"
        have "LanguageCon.com.Skip = Q"
          by (metis (no_types) \<open>(n, \<Gamma>, cfg) \<in> cptn_mod_nest_call\<close> cfg cptn_dest1_pair cptn_if_cptn_mod cptn_mod_nest_cptn_mod fst_conv last.simps last_length length_Cons lessI not_Cons_self2 skip_all_skip)
        then show ?thesis
          using a1 by (meson Cons.hyps)
      qed      
  qed
qed

lemma throw_min_nested_call_0:
  assumes a0:"min_call n \<Gamma> cfg" and
          a1:"cfg = (Throw,s)#cfg1"
  shows "n=0"
proof -
  have asm0:"(n, \<Gamma>, cfg) \<in> cptn_mod_nest_call" and 
       asm1:"(\<forall>m<n. (m, \<Gamma>, cfg) \<notin> cptn_mod_nest_call)"  
       using a0 unfolding min_call_def by auto  
  show ?thesis using a1 asm0 asm1
  proof (induct cfg1 arbitrary: cfg s n)
    case Nil thus ?case
      using cptn_mod_nest_call.CptnModNestOne neq0_conv by blast
  next
    case (Cons x xs)
      then obtain s' where x:"x = (Skip,s') \<or> x = (Throw, s')"
         using CptnMod_elim_cases(10) cptn_eq_cptn_mod_set
         by (metis cptn_mod_nest_cptn_mod)      
      then obtain Q where cfg:"cfg = (LanguageCon.com.Throw, s) # (Q,s') # xs"
        using Cons  by force
      then have min_call:"min_call n \<Gamma> cfg" using Cons unfolding min_call_def by auto
      then have "(\<forall>f. SmallStepCon.redex Skip \<noteq> LanguageCon.com.Call f)" by auto
      then have min_call':"min_call n \<Gamma> ((Q, s')#xs)" 
        using elim_cptn_mod_min_nest_call[OF min_call cfg] cfg
        by simp
      from x show ?case
      proof
        assume "x=(Skip,s')"
        thus ?thesis using skip_min_nested_call_0 min_call' Cons(2) cfg by fastforce
      next       
        assume "x=(Throw,s')"
        thus ?thesis using Cons(1,2) min_call' cfg unfolding min_call_def  
          by blast 
      qed      
  qed
qed



text {* function to calculate that there is not any subsequent where the nested call is n *}
definition cond_seq_1
where 
"cond_seq_1 n \<Gamma> c1 s xs c2 zs ys \<equiv> ((n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call \<and> 
                       fst(last((c1,s)#xs)) = Skip \<and>
                        (n,\<Gamma>,((c2, snd(last ((c1, s)#xs)))#ys)) \<in> cptn_mod_nest_call \<and>
                       zs=(map (lift c2) xs)@((c2, snd(last ((c1, s)#xs)))#ys))"

definition cond_seq_2
where
"cond_seq_2 n \<Gamma> c1 s xs c2 zs ys s' s'' \<equiv>  s= Normal s'' \<and> 
                    (n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call \<and> 
                    fst(last ((c1, s)#xs)) = Throw \<and>
                    snd(last ((c1, s)#xs)) = Normal s' \<and> 
                    (n,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call \<and> 
                     zs=(map (lift c2) xs)@((Throw,Normal s')#ys)"

definition cond_catch_1
where 
"cond_catch_1 n \<Gamma> c1 s xs c2 zs ys \<equiv> ((n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call \<and> 
                       fst(last((c1,s)#xs)) = Skip \<and>
                        (n,\<Gamma>,((Skip, snd(last ((c1, s)#xs)))#ys)) \<in> cptn_mod_nest_call \<and>
                       zs=(map (lift_catch c2) xs)@((Skip, snd(last ((c1, s)#xs)))#ys))"

definition cond_catch_2
where
"cond_catch_2 n \<Gamma> c1 s xs c2 zs ys s' s'' \<equiv> s= Normal s'' \<and> 
                    (n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call \<and> 
                    fst(last ((c1, s)#xs)) = Throw \<and>
                    snd(last ((c1, s)#xs)) = Normal s' \<and> 
                    (n,\<Gamma>,(c2,Normal s')#ys) \<in> cptn_mod_nest_call \<and> 
                     zs=(map (lift_catch c2) xs)@((c2,Normal s')#ys)"

fun biggest_nest_call :: "('s,'p,'f,'e)com \<Rightarrow> 
                         ('s,'f) xstate \<Rightarrow> 
                         (('s,'p,'f,'e) config) list \<Rightarrow> 
                         ('s,'p,'f,'e) body \<Rightarrow> 
                         nat \<Rightarrow> bool"
where
 "biggest_nest_call (Seq c1 c2) s zs \<Gamma> n  = 
   (if (\<exists>xs. ((min_call n \<Gamma> ((c1,s)#xs)) \<and> (zs=map (lift c2) xs))) then
       let xsa = (SOME xs. (min_call n \<Gamma> ((c1,s)#xs)) \<and> (zs=map (lift c2) xs)) in
       (biggest_nest_call c1 s xsa \<Gamma> n)
    else if (\<exists>xs ys. cond_seq_1 n \<Gamma> c1 s xs c2 zs ys) then
         let xsa = (SOME xs. \<exists>ys. cond_seq_1 n \<Gamma> c1 s xs c2 zs ys);
             ysa = (SOME ys. cond_seq_1 n \<Gamma> c1 s xsa c2 zs ys) in
         if (min_call n \<Gamma> ((c2, snd(last ((c1, s)#xsa)))#ysa)) then True
         else (biggest_nest_call c1 s xsa \<Gamma> n)            
   else let xsa = (SOME xs. \<exists>ys s' s''. cond_seq_2 n \<Gamma> c1 s xs c2 zs ys s' s'') in
           (biggest_nest_call c1 s xsa \<Gamma> n))"      
|"biggest_nest_call (Catch c1 c2) s zs \<Gamma> n  = 
  (if (\<exists>xs. ((min_call n \<Gamma> ((c1,s)#xs)) \<and> (zs=map (lift_catch c2) xs))) then
    let xsa = (SOME xs. (min_call n \<Gamma> ((c1,s)#xs)) \<and> (zs=map (lift_catch c2) xs)) in
       (biggest_nest_call c1 s xsa \<Gamma> n)
    else if (\<exists>xs ys. cond_catch_1 n \<Gamma> c1 s xs c2 zs ys) then
         let xsa = (SOME xs. \<exists>ys. cond_catch_1 n \<Gamma> c1 s xs c2 zs ys) in            
                 (biggest_nest_call c1 s xsa \<Gamma> n)
   else let xsa = (SOME xs. \<exists>ys s' s''. cond_catch_2 n \<Gamma> c1 s xs c2 zs ys s' s'');
            ysa = (SOME ys. \<exists>s' s''. cond_catch_2 n \<Gamma> c1 s xsa c2 zs ys s' s'') in
         if (min_call n \<Gamma> ((c2, snd(last ((c1, s)#xsa)))#ysa)) then True
         else (biggest_nest_call c1 s xsa \<Gamma> n))"
|"biggest_nest_call _ _ _ _ _ = False"


lemma min_call_less_eq_n:
  "(n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call \<Longrightarrow>     
   (n,\<Gamma>,(c2, snd(last ((c1, s)#xs)))#ys) \<in> cptn_mod_nest_call \<Longrightarrow>
   min_call p \<Gamma> ((c1, s)#xs) \<and> min_call q \<Gamma> ((c2, snd(last ((c1, s)#xs)))#ys) \<Longrightarrow>
   p\<le>n \<and> q\<le>n"
unfolding min_call_def
using le_less_linear by blast

lemma min_call_seq_less_eq_n':
  "(n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call \<Longrightarrow>     
   min_call p \<Gamma> ((c1, s)#xs)  \<Longrightarrow>
   p\<le>n"
unfolding min_call_def
using le_less_linear by blast

lemma min_call_seq2:
  "min_call n \<Gamma> ((Seq c1 c2,s)#zs) \<Longrightarrow>
   (n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call \<Longrightarrow> 
    fst(last ((c1, s)#xs)) = Skip \<Longrightarrow>
   (n,\<Gamma>,(c2, snd(last ((c1, s)#xs)))#ys) \<in> cptn_mod_nest_call \<Longrightarrow>
    zs=(map (lift c2) xs)@((c2, snd(last ((c1, s)#xs)))#ys) \<Longrightarrow>
   min_call n \<Gamma> ((c1, s)#xs) \<or> min_call n \<Gamma> ((c2, snd(last ((c1, s)#xs)))#ys)
   "
proof -
  assume a0:"min_call n \<Gamma> ((Seq c1 c2,s)#zs)" and
         a1:"(n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call" and
         a2:"fst(last ((c1, s)#xs)) = Skip" and
         a3:"(n,\<Gamma>,(c2, snd(last ((c1, s)#xs)))#ys) \<in> cptn_mod_nest_call" and
         a4:"zs=(map (lift c2) xs)@((c2, snd(last ((c1, s)#xs)))#ys)"
  then obtain p q where min_calls: 
    "min_call p \<Gamma> ((c1, s)#xs) \<and> min_call q \<Gamma> ((c2, snd(last ((c1, s)#xs)))#ys)"
    using a1 a3 minimum_nest_call by blast
  then have p_q:"p\<le>n \<and> q\<le>n" using a0 a1  a3 a4 min_call_less_eq_n by blast
  {
    assume ass0:"p<n \<and> q <n"     
    then have "(p,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call" and
              "(q,\<Gamma>,(c2, snd(last ((c1, s)#xs)))#ys) \<in> cptn_mod_nest_call"
      using min_calls unfolding min_call_def by auto
    then have ?thesis
    proof (cases "p\<le>q")
      case True 
      then have q_cptn_c1:"(q, \<Gamma>, (c1, s) # xs) \<in> cptn_mod_nest_call" 
        using cptn_mod_nest_mono min_calls unfolding min_call_def  
        by blast
      have q_cptn_c2:"(q, \<Gamma>, (c2, snd (last ((c1, s) # xs))) # ys) \<in> cptn_mod_nest_call"
       using min_calls unfolding min_call_def by auto
      then have "(q,\<Gamma>,((Seq c1 c2,s)#zs)) \<in>cptn_mod_nest_call"
        using True min_calls a2 a4  CptnModNestSeq2[OF q_cptn_c1 a2 q_cptn_c2 a4] 
        by auto
      thus ?thesis using ass0 a0 unfolding min_call_def by auto
    next
      case False
      then have q_cptn_c1:"(p, \<Gamma>, (c1, s) # xs) \<in> cptn_mod_nest_call" 
        using  min_calls unfolding min_call_def  
        by blast
      have q_cptn_c2:"(p, \<Gamma>, (c2, snd (last ((c1, s) # xs))) # ys) \<in> cptn_mod_nest_call"
       using min_calls False unfolding min_call_def
       by (metis (no_types, lifting) cptn_mod_nest_mono2 not_less)
      then have "(p,\<Gamma>,((Seq c1 c2,s)#zs)) \<in>cptn_mod_nest_call"
        using False min_calls a2 a4  CptnModNestSeq2[OF q_cptn_c1 a2 q_cptn_c2 a4] 
        by auto
      thus ?thesis using ass0 a0 unfolding min_call_def by auto
    qed
  }note l=this
  {
    assume ass0:"p\<ge>n \<or> q \<ge>n" 
    then have ?thesis using p_q min_calls by fastforce
  }
  thus ?thesis using l by fastforce
qed

lemma min_call_seq3:
  "min_call n \<Gamma> ((Seq c1 c2,s)#zs) \<Longrightarrow>
   s= Normal s'' \<Longrightarrow>
   (n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call \<Longrightarrow> 
    fst(last ((c1, s)#xs)) = Throw \<Longrightarrow>
    snd(last ((c1, s)#xs)) = Normal s' \<Longrightarrow>
   (n,\<Gamma>,(Throw, snd(last ((c1, s)#xs)))#ys) \<in> cptn_mod_nest_call \<Longrightarrow>
    zs=(map (lift c2) xs)@((Throw, snd(last ((c1, s)#xs)))#ys) \<Longrightarrow>
   min_call n \<Gamma> ((c1, s)#xs)
   "
proof -
  assume a0:"min_call n \<Gamma> ((Seq c1 c2,s)#zs)" and
         a0':"s= Normal s''" and
         a1:"(n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call" and
         a2:"fst(last ((c1, s)#xs)) = Throw" and
         a2':"snd(last ((c1, s)#xs)) = Normal s'" and
         a3:"(n,\<Gamma>,(Throw, snd(last ((c1, s)#xs)))#ys) \<in> cptn_mod_nest_call" and
         a4:"zs=(map (lift c2) xs)@((Throw, snd(last ((c1, s)#xs)))#ys)"
  then obtain p where min_calls: 
    "min_call p \<Gamma> ((c1, s)#xs) \<and> min_call 0 \<Gamma> ((Throw, snd(last ((c1, s)#xs)))#ys)"
    using a1 a3 minimum_nest_call throw_min_nested_call_0  by metis
  then have p_q:"p\<le>n \<and> 0\<le>n" using a0 a1  a3 a4 min_call_less_eq_n by blast
  {
    assume ass0:"p<n \<and> 0 <n"     
    then have "(p,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call" and
              "(0,\<Gamma>,(Throw, snd(last ((c1, s)#xs)))#ys) \<in> cptn_mod_nest_call"
      using min_calls unfolding min_call_def by auto
    then have ?thesis
    proof (cases "p\<le>0")
      case True 
      then have q_cptn_c1:"(0, \<Gamma>, (c1, Normal s'') # xs) \<in> cptn_mod_nest_call" 
        using cptn_mod_nest_mono min_calls a0' unfolding min_call_def  
        by blast
      have q_cptn_c2:"(0, \<Gamma>, (Throw, snd (last ((c1, s) # xs))) # ys) \<in> cptn_mod_nest_call"
       using min_calls unfolding min_call_def by auto
      then have "(0,\<Gamma>,((Seq c1 c2,s)#zs)) \<in>cptn_mod_nest_call"
        using True min_calls a2 a4 a2' a0'  CptnModNestSeq3[OF q_cptn_c1 ] 
        by auto
      thus ?thesis using ass0 a0 unfolding min_call_def by auto
    next
      case False
      then have q_cptn_c1:"(p, \<Gamma>, (c1, Normal s'') # xs) \<in> cptn_mod_nest_call" 
        using  min_calls a0' unfolding min_call_def  
        by blast
      have q_cptn_c2:"(p, \<Gamma>, (Throw, snd (last ((c1, s) # xs))) # ys) \<in> cptn_mod_nest_call"
       using min_calls False unfolding min_call_def
       by (metis (no_types, lifting) cptn_mod_nest_mono2 not_less)
      then have "(p,\<Gamma>,((Seq c1 c2,s)#zs)) \<in>cptn_mod_nest_call"
        using False min_calls a2 a4 a0' a2'  CptnModNestSeq3[OF q_cptn_c1]
        by auto       
      thus ?thesis using ass0 a0 unfolding min_call_def by auto
    qed
  }note l=this
  {
    assume ass0:"p\<ge>n \<or> 0 \<ge>n" 
    then have ?thesis using p_q min_calls by fastforce
  }
  thus ?thesis using l by fastforce
qed

lemma min_call_catch2:
  "min_call n \<Gamma> ((Catch c1 c2,s)#zs) \<Longrightarrow>   
   (n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call \<Longrightarrow> 
    fst(last ((c1, s)#xs)) = Skip \<Longrightarrow>    
   (n,\<Gamma>,(Skip, snd(last ((c1, s)#xs)))#ys) \<in> cptn_mod_nest_call \<Longrightarrow>
    zs=(map (lift_catch c2) xs)@((Skip, snd(last ((c1, s)#xs)))#ys) \<Longrightarrow>
   min_call n \<Gamma> ((c1, s)#xs)
   "
proof -
  assume a0:"min_call n \<Gamma> ((Catch c1 c2,s)#zs)" and        
         a1:"(n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call" and
         a2:"fst(last ((c1, s)#xs)) = Skip" and        
         a3:"(n,\<Gamma>,(Skip, snd(last ((c1, s)#xs)))#ys) \<in> cptn_mod_nest_call" and
         a4:"zs=(map (lift_catch c2) xs)@((Skip, snd(last ((c1, s)#xs)))#ys)"
  then obtain p where min_calls: 
    "min_call p \<Gamma> ((c1, s)#xs) \<and> min_call 0 \<Gamma> ((Skip, snd(last ((c1, s)#xs)))#ys)"
    using a1 a3 minimum_nest_call skip_min_nested_call_0  by metis
  then have p_q:"p\<le>n \<and> 0\<le>n" using a0 a1  a3 a4 min_call_less_eq_n by blast
  {
    assume ass0:"p<n \<and> 0 <n"     
    then have "(p,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call" and
              "(0,\<Gamma>,(Skip, snd(last ((c1, s)#xs)))#ys) \<in> cptn_mod_nest_call"
      using min_calls unfolding min_call_def by auto
    then have ?thesis
    proof (cases "p\<le>0")
      case True 
      then have q_cptn_c1:"(0, \<Gamma>, (c1, s) # xs) \<in> cptn_mod_nest_call" 
        using cptn_mod_nest_mono min_calls  unfolding min_call_def  
        by blast
      have q_cptn_c2:"(0, \<Gamma>, (Skip, snd (last ((c1, s) # xs))) # ys) \<in> cptn_mod_nest_call"
       using min_calls unfolding min_call_def by auto
      then have "(0,\<Gamma>,((Catch c1 c2,s)#zs)) \<in>cptn_mod_nest_call"
        using True min_calls a2 a4    CptnModNestCatch2[OF q_cptn_c1 ] 
        by auto
      thus ?thesis using ass0 a0 unfolding min_call_def by auto
    next
      case False
      then have q_cptn_c1:"(p, \<Gamma>, (c1, s) # xs) \<in> cptn_mod_nest_call" 
        using  min_calls  unfolding min_call_def  
        by blast
      have q_cptn_c2:"(p, \<Gamma>, (Skip, snd (last ((c1, s) # xs))) # ys) \<in> cptn_mod_nest_call"
       using min_calls False unfolding min_call_def
       by (metis (no_types, lifting) cptn_mod_nest_mono2 not_less)
      then have "(p,\<Gamma>,((Catch c1 c2,s)#zs)) \<in>cptn_mod_nest_call"
        using False min_calls a2 a4   CptnModNestCatch2[OF q_cptn_c1]
        by auto       
      thus ?thesis using ass0 a0 unfolding min_call_def by auto
    qed
  }note l=this
  {
    assume ass0:"p\<ge>n \<or> 0 \<ge>n" 
    then have ?thesis using p_q min_calls by fastforce
  }
  thus ?thesis using l by fastforce
qed

lemma min_call_catch_less_eq_n:
  "(n,\<Gamma>, (c1, Normal s)#xs) \<in> cptn_mod_nest_call \<Longrightarrow>        
   (n,\<Gamma>,(c2, snd(last ((c1, Normal s)#xs)))#ys) \<in> cptn_mod_nest_call \<Longrightarrow>    
   min_call p \<Gamma> ((c1, Normal s)#xs) \<and> min_call q \<Gamma> ((c2, snd(last ((c1, Normal s)#xs)))#ys) \<Longrightarrow>
   p\<le>n \<and> q\<le>n"
unfolding min_call_def
using le_less_linear by blast

lemma min_call_catch3:
  "min_call n \<Gamma> ((Catch c1 c2,Normal s)#zs) \<Longrightarrow>
   (n,\<Gamma>, (c1, Normal s)#xs) \<in> cptn_mod_nest_call \<Longrightarrow> 
    fst(last ((c1, Normal s)#xs)) = Throw \<Longrightarrow>
    snd(last ((c1, Normal s)#xs)) = Normal s' \<Longrightarrow>
   (n,\<Gamma>,(c2, snd(last ((c1, Normal s)#xs)))#ys) \<in> cptn_mod_nest_call \<Longrightarrow>
    zs=(map (lift_catch c2) xs)@((c2, snd(last ((c1, Normal s)#xs)))#ys) \<Longrightarrow>
   min_call n \<Gamma> ((c1, Normal s)#xs) \<or> min_call n \<Gamma> ((c2, snd(last ((c1, Normal s)#xs)))#ys)
   "
proof -
  assume a0:"min_call n \<Gamma> ((Catch c1 c2,Normal s)#zs)" and
         a1:"(n,\<Gamma>, (c1, Normal s)#xs) \<in> cptn_mod_nest_call" and
         a2:"fst(last ((c1, Normal s)#xs)) = Throw" and
         a2':"snd(last ((c1, Normal s)#xs)) = Normal s'" and
         a3:"(n,\<Gamma>,(c2, snd(last ((c1, Normal s)#xs)))#ys) \<in> cptn_mod_nest_call" and
         a4:"zs=(map (lift_catch c2) xs)@((c2, snd(last ((c1, Normal s)#xs)))#ys)"
  then obtain p q where min_calls: 
    "min_call p \<Gamma> ((c1, Normal s)#xs) \<and> min_call q \<Gamma> ((c2, snd(last ((c1, Normal s)#xs)))#ys)"
    using a1 a3 minimum_nest_call by blast
  then have p_q:"p\<le>n \<and> q\<le>n" 
    using a1 a2 a2' a3 a4 min_call_less_eq_n by blast
  {
    assume ass0:"p<n \<and> q <n"     
    then have "(p,\<Gamma>, (c1, Normal s)#xs) \<in> cptn_mod_nest_call" and
              "(q,\<Gamma>,(c2, snd(last ((c1, Normal s)#xs)))#ys) \<in> cptn_mod_nest_call"
      using min_calls unfolding min_call_def by auto
    then have ?thesis
    proof (cases "p\<le>q")
      case True 
      then have q_cptn_c1:"(q, \<Gamma>, (c1,Normal s) # xs) \<in> cptn_mod_nest_call" 
        using cptn_mod_nest_mono min_calls unfolding min_call_def  
        by blast
      have q_cptn_c2:"(q, \<Gamma>, (c2, snd (last ((c1, Normal s) # xs))) # ys) \<in> cptn_mod_nest_call"
       using min_calls unfolding min_call_def by auto
      then have "(q,\<Gamma>,((Catch c1 c2, Normal s)#zs)) \<in>cptn_mod_nest_call"
        using True min_calls a2 a2' a4  CptnModNestCatch3[OF q_cptn_c1 a2 a2' q_cptn_c2 a4] 
        by auto
      thus ?thesis using ass0 a0 unfolding min_call_def by auto
    next
      case False
      then have q_cptn_c1:"(p, \<Gamma>, (c1, Normal s) # xs) \<in> cptn_mod_nest_call" 
        using  min_calls unfolding min_call_def  
        by blast
      have q_cptn_c2:"(p, \<Gamma>, (c2, snd (last ((c1, Normal s) # xs))) # ys) \<in> cptn_mod_nest_call"
       using min_calls False unfolding min_call_def
       by (metis (no_types, lifting) cptn_mod_nest_mono2 not_less)
      then have "(p,\<Gamma>,((Catch c1 c2,Normal s)#zs)) \<in>cptn_mod_nest_call"
        using False min_calls a2 a4  CptnModNestCatch3[OF q_cptn_c1 a2 a2' q_cptn_c2 a4] 
        by auto
      thus ?thesis using ass0 a0 unfolding min_call_def by auto
    qed
  }note l=this
  {
    assume ass0:"p\<ge>n \<or> q \<ge>n" 
    then have ?thesis using p_q min_calls by fastforce
  }
  thus ?thesis using l by fastforce
qed

lemma min_call_seq_c1_not_finish:
  "min_call n \<Gamma> cfg \<Longrightarrow>
   cfg = (LanguageCon.com.Seq P0 P1, s) # (Q, t) # cfg1 \<Longrightarrow>
   (n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call \<Longrightarrow>
   (Q, t) # cfg1 = map (lift P1) xs \<Longrightarrow>
   min_call  n \<Gamma> ((P0, s)#xs)
   "
proof -
  assume a0:"min_call n \<Gamma> cfg" and
        a1:" cfg = (LanguageCon.com.Seq P0 P1, s) # (Q, t) # cfg1" and
        a2:"(n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call" and
        a3:"(Q, t) # cfg1 = map (lift P1) xs" 
  then have "(n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call" using a2 by auto
  moreover have "\<forall>m<n. (m, \<Gamma>,(P0, s)#xs) \<notin> cptn_mod_nest_call"
  proof-
    {fix m
     assume ass:"m<n"
     {  assume ass1:"(m, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call"
       then have "(m,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" 
         using a1 a3 CptnModNestSeq1[OF ass1] by auto
       then have False using ass a0 unfolding min_call_def by auto
     }
     then have "(m, \<Gamma>, (P0, s) # xs) \<notin> cptn_mod_nest_call" by auto
    } then show ?thesis by auto
  qed
  ultimately show ?thesis unfolding min_call_def by auto
qed

lemma min_call_seq_not_finish:
  " min_call  n \<Gamma> ((P0, s)#xs) \<Longrightarrow>
   cfg = (LanguageCon.com.Seq P0 P1, s) #  cfg1 \<Longrightarrow>  
    cfg1 = map (lift P1) xs \<Longrightarrow>
   min_call n \<Gamma> cfg 
   "
proof -
  assume a0:"min_call  n \<Gamma> ((P0, s)#xs)" and
        a1:" cfg = (LanguageCon.com.Seq P0 P1, s) #  cfg1" and        
        a2:" cfg1 = map (lift P1) xs" 
  then have "(n, \<Gamma>,cfg) \<in> cptn_mod_nest_call" 
    using a0 a1 a2 CptnModNestSeq1[of n \<Gamma> P0 s xs "cfg1" P1] unfolding min_call_def 
    by auto
  moreover have "\<forall>m<n. (m, \<Gamma>,cfg) \<notin> cptn_mod_nest_call"
  proof-
    {fix m
     assume ass:"m<n"
     {  assume ass1:"(m, \<Gamma>, cfg) \<in> cptn_mod_nest_call"
       then have "(m,\<Gamma>,(P0, s)#xs) \<in>  cptn_mod_nest_call" 
         using a1 a2 by (metis (no_types) Seq_P_Not_finish div_seq_nest) 
       then have False using ass a0 unfolding min_call_def by auto
     }
     then have "(m, \<Gamma>, cfg) \<notin> cptn_mod_nest_call" by auto
    } then show ?thesis by auto
  qed
  ultimately show ?thesis unfolding min_call_def by auto
qed

lemma min_call_catch_c1_not_finish:
  "min_call n \<Gamma> cfg \<Longrightarrow>
   cfg = (LanguageCon.com.Catch P0 P1, s) # (Q, t) # cfg1 \<Longrightarrow>
   (n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call \<Longrightarrow>
   (Q, t) # cfg1 = map (lift_catch P1) xs \<Longrightarrow>
   min_call  n \<Gamma> ((P0, s)#xs)
   "
proof -
  assume a0:"min_call n \<Gamma> cfg" and
        a1:" cfg = (LanguageCon.com.Catch P0 P1, s) # (Q, t) # cfg1" and
        a2:"(n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call" and
        a3:"(Q, t) # cfg1 = map (lift_catch P1) xs" 
  then have "(n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call" using a2 by auto
  moreover have "\<forall>m<n. (m, \<Gamma>,(P0, s)#xs) \<notin> cptn_mod_nest_call"
  proof-
    {fix m
     assume ass:"m<n"
     {  assume ass1:"(m, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call"
       then have "(m,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" 
         using a1 a3 CptnModNestCatch1[OF ass1] by auto
       then have False using ass a0 unfolding min_call_def by auto
     }
     then have "(m, \<Gamma>, (P0, s) # xs) \<notin> cptn_mod_nest_call" by auto
    } then show ?thesis by auto
  qed
  ultimately show ?thesis unfolding min_call_def by auto
qed

lemma min_call_catch_not_finish:
  " min_call  n \<Gamma> ((P0, s)#xs) \<Longrightarrow>
   cfg = (LanguageCon.com.Catch P0 P1, s) #  cfg1 \<Longrightarrow>  
    cfg1 = map (lift_catch P1) xs \<Longrightarrow>
   min_call n \<Gamma> cfg 
   "
proof -
  assume a0:"min_call  n \<Gamma> ((P0, s)#xs)" and
        a1:" cfg = (Catch P0 P1, s) #  cfg1" and        
        a2:" cfg1 = map (lift_catch P1) xs" 
  then have "(n, \<Gamma>,cfg) \<in> cptn_mod_nest_call" 
    using a0 a1 a2 CptnModNestCatch1[of n \<Gamma> P0 s xs "cfg1" P1] unfolding min_call_def 
    by auto
  moreover have "\<forall>m<n. (m, \<Gamma>,cfg) \<notin> cptn_mod_nest_call"
  proof-
    {fix m
     assume ass:"m<n"
     {  assume ass1:"(m, \<Gamma>, cfg) \<in> cptn_mod_nest_call"
       then have "(m,\<Gamma>,(P0, s)#xs) \<in>  cptn_mod_nest_call" 
         using a1 a2 by (metis (no_types) Catch_P_Not_finish div_catch_nest) 
       then have False using ass a0 unfolding min_call_def by auto
     }
     then have "(m, \<Gamma>, cfg) \<notin> cptn_mod_nest_call" by auto
    } then show ?thesis by auto
  qed
  ultimately show ?thesis unfolding min_call_def by auto
qed

lemma seq_xs_no_empty: assumes
     seq:"seq_cond_nest ((Q,t)#cfg1) P1 xs P0 s s'' s' \<Gamma> n" and
     cfg:"cfg = (LanguageCon.com.Seq P0 P1, s) # (Q, t) # cfg1" and
     a0:"SmallStepCon.redex (LanguageCon.com.Seq P0 P1) = LanguageCon.com.Call f"
     shows"\<exists>Q' xs'. Q=Seq Q' P1 \<and> xs=(Q',t)#xs'"
using seq
unfolding lift_def seq_cond_nest_def
proof
    assume "(Q, t) # cfg1 = map (\<lambda>(P, s). (LanguageCon.com.Seq P P1, s)) xs"
    thus ?thesis by auto
next
  assume "fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Skip \<and>
        (\<exists>ys. (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
              (Q, t) # cfg1 =
              map (\<lambda>(P, s). (LanguageCon.com.Seq P P1, s)) xs @
              (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<or>
        fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and>
        snd (last ((P0, s) # xs)) = Normal s' \<and>
        s = Normal s'' \<and>
        (\<exists>ys. (n, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call \<and>
              (Q, t) # cfg1 =
              map (\<lambda>(P, s). (LanguageCon.com.Seq P P1, s)) xs @
              (LanguageCon.com.Throw, Normal s') # ys)"
  thus ?thesis
  proof 
    assume ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Skip \<and>
        (\<exists>ys. (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
              (Q, t) # cfg1 =
              map (\<lambda>(P, s). (LanguageCon.com.Seq P P1, s)) xs @
              (P1, snd (((P0, s) # xs) ! length xs)) # ys)"
    show ?thesis 
    proof (cases xs)
      case Nil thus ?thesis using cfg a0 ass by auto
    next
      case (Cons xa xsa)
      then obtain a b where xa:"xa = (a,b)" by fastforce
      obtain pps :: "(('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate) list" where
            "(Q, t) # cfg1 = ((case (a, b) of (c, x) \<Rightarrow> (LanguageCon.com.Seq c P1, x)) # map (\<lambda>(c, y). 
                             (LanguageCon.com.Seq c P1, y)) xsa) @ 
                             (P1, snd (((P0, s) # xs) ! length xs)) # pps"
        using xa ass local.Cons by moura
       then show ?thesis
         by (simp add: xa local.Cons)
    qed      
  next
    assume ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and>
        snd (last ((P0, s) # xs)) = Normal s' \<and>
        s = Normal s'' \<and>
        (\<exists>ys. (n, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call \<and>
              (Q, t) # cfg1 =
              map (\<lambda>(P, s). (LanguageCon.com.Seq P P1, s)) xs @
              (LanguageCon.com.Throw, Normal s') # ys)"
    thus ?thesis
    proof (cases xs)
      case Nil thus ?thesis using cfg a0 ass by auto
    next
      case (Cons xa xsa)
      then obtain a b where xa:"xa = (a,b)" by fastforce
      obtain pps :: "(('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate) list" where
        "(Q, t) # cfg1 = ((case (a, b) of (c, x) \<Rightarrow> (LanguageCon.com.Seq c P1, x)) # map (\<lambda>(c, y). 
              (LanguageCon.com.Seq c P1, y)) xsa) @ (LanguageCon.com.Throw, Normal s') # pps"
        using ass local.Cons xa by force
      then show ?thesis
        by (simp add: local.Cons xa)
    qed           
  qed
qed

lemma catch_xs_no_empty: assumes
     seq:"catch_cond_nest ((Q,t)#cfg1) P1 xs P0 s s'' s' \<Gamma> n" and
     cfg:"cfg = (LanguageCon.com.Catch P0 P1, s) # (Q, t) # cfg1" and
     a0:"SmallStepCon.redex (LanguageCon.com.Catch P0 P1) = LanguageCon.com.Call f"
     shows"\<exists>Q' xs'. Q=Catch Q' P1 \<and> xs=(Q',t)#xs'"
using seq
unfolding lift_catch_def catch_cond_nest_def
proof
    assume "(Q, t) # cfg1 = map (\<lambda>(P, s). (LanguageCon.com.Catch P P1, s)) xs"
    thus ?thesis by auto
next
  assume "fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and>
    snd (last ((P0, s) # xs)) = Normal s' \<and>
    s = Normal s'' \<and>
    (\<exists>ys. (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
          (Q, t) # cfg1 = map (\<lambda>(P, s). (LanguageCon.com.Catch P P1, s)) xs @ 
                                          (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<or>
    fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Skip \<and>
    (\<exists>ys. (n, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
          (Q, t) # cfg1 =
          map (\<lambda>(P, s). (LanguageCon.com.Catch P P1, s)) xs @ 
                         (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys)"
  thus ?thesis
  proof 
    assume ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and>
                snd (last ((P0, s) # xs)) = Normal s' \<and>
                s = Normal s'' \<and>
                (\<exists>ys. (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
                  (Q, t) # cfg1 = map (\<lambda>(P, s). (LanguageCon.com.Catch P P1, s)) xs @ 
                                          (P1, snd (((P0, s) # xs) ! length xs)) # ys)"
    show ?thesis 
    proof (cases xs)
      case Nil thus ?thesis using cfg a0 ass by auto
    next
      case (Cons xa xsa)
      then obtain a b where xa:"xa = (a,b)" by fastforce
      obtain pps :: "(('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate) list" where
       "(Q, t) # cfg1 = ((case (a, b) of (c, x) \<Rightarrow> (LanguageCon.com.Catch c P1, x)) # 
            map (\<lambda>(c, y). (LanguageCon.com.Catch c P1, y)) xsa) @ 
                           (P1, snd (((P0, s) # xs) ! length xs)) # pps"
       using ass local.Cons xa by moura
     then show ?thesis
       by (simp add: local.Cons xa)
    qed     
  next
    assume ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Skip \<and>
    (\<exists>ys. (n, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
          (Q, t) # cfg1 =
          map (\<lambda>(P, s). (LanguageCon.com.Catch P P1, s)) xs @ 
                         (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys)"
    thus ?thesis
    proof (cases xs)
      case Nil thus ?thesis using cfg a0 ass by auto
    next
      case (Cons xa xsa)
      then obtain a b where xa:"xa = (a,b)" by fastforce      
      obtain pps :: "(('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate) list" where
        "(Q, t) # cfg1 = ((case (a, b) of (c, x) \<Rightarrow> 
           (LanguageCon.com.Catch c P1, x)) # map (\<lambda>(c, y). 
             (LanguageCon.com.Catch c P1, y)) xsa) @ 
               (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # pps"
        using ass local.Cons xa by force
      then show ?thesis
        by (simp add: local.Cons xa)
    qed        
  qed
qed

lemma redex_call_cptn_mod_min_nest_call_gr_zero:
 assumes a0:"min_call n \<Gamma> cfg" and
         a1:"cfg = (P,s)#(Q,t)#cfg1" and
         a2:"redex P = Call f \<and>  
             \<Gamma> f = Some bdy \<and> (\<exists>sa. s=Normal sa) \<and> t=s" and
         a3:"\<Gamma>\<turnstile>\<^sub>c(P,s)\<rightarrow>(Q,t)"
 shows "n>0"
using a0 a1 a2 a3
proof (induct P arbitrary: Q cfg1 cfg s t n)
  case (Call f1) thus ?case
   by (metis SmallStepCon.redex.simps(7) elim_cptn_mod_nest_call_n_greater_zero min_call_def option.distinct(1) stepc_Normal_elim_cases(9))
next
  case (Seq P0 P1) 
  then obtain xs s' s'' where 
          p0_cptn:"(n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call"  and 
          seq:"seq_cond_nest ((Q,t)#cfg1) P1 xs P0 s s'' s' \<Gamma> n"
  using div_seq_nest[of n \<Gamma> cfg] unfolding min_call_def by blast
  then obtain m where min:"min_call m \<Gamma> ((P0, s)#xs)"
    using minimum_nest_call by blast 
  have xs':"\<exists>Q' xs'. Q=Seq Q' P1 \<and> xs=(Q',t)#xs'"
     using seq Seq seq_xs_no_empty by auto 
  then have "0<m" using Seq(1,5,6) min
    using SmallStepCon.redex.simps(4) stepc_elim_cases_Seq_Seq by fastforce
  thus ?case by (metis min min_call_def not_gr0 p0_cptn) 
next
  case (Catch P0 P1)
 then obtain xs s' s'' where 
          p0_cptn:"(n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call"  and 
          seq:"catch_cond_nest ((Q,t)#cfg1) P1 xs P0 s s'' s' \<Gamma> n"
  using div_catch_nest[of n \<Gamma> cfg] unfolding min_call_def by blast
  then obtain m where min:"min_call m \<Gamma> ((P0, s)#xs)"
    using minimum_nest_call by blast 
  obtain Q' xs' where xs':"Q=Catch Q' P1 \<and> xs=(Q',t)#xs'"
     using catch_xs_no_empty[OF seq Catch(4)] Catch by blast
  then have "0<m" using Catch(1,5,6) min
    using SmallStepCon.redex.simps(4) stepc_elim_cases_Catch_Catch by fastforce
  thus ?case by (metis min min_call_def not_gr0 p0_cptn)
qed(auto)

  

lemma elim_redex_call_cptn_mod_min_nest_call:
 assumes a0:"min_call n \<Gamma> cfg" and
         a1:"cfg = (P,s)#(Q,t)#cfg1" and
         a2:"redex P = Call f \<and>  
             \<Gamma> f = Some bdy \<and> (\<exists>sa. s=Normal sa) \<and> t=s " and
         a3:"biggest_nest_call P s ((Q,t)#cfg1) \<Gamma> n"  
 shows "min_call n \<Gamma> ((Q,t)#cfg1)"
using a0 a1 a2 a3 
proof (induct P arbitrary: Q cfg1 cfg s t n)  
  case Cond thus ?case by fastforce
next
  case (Seq P0 P1) 
  then obtain xs s' s'' where 
          p0_cptn:"(n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call"  and 
          seq:"seq_cond_nest ((Q,t)#cfg1) P1 xs P0 s s'' s' \<Gamma> n"
  using div_seq_nest[of n \<Gamma> cfg] unfolding min_call_def by blast
  
  show ?case using seq unfolding seq_cond_nest_def 
  proof
    assume ass:"(Q, t) # cfg1 = map (lift P1) xs"   
    then obtain Q' xs' where xs':"Q=Seq Q' P1 \<and> xs=(Q',t)#xs'"
      unfolding lift_def by fastforce
    then have ctpn_P0:"(P0, s) # xs = (P0, s) # (Q', t) # xs'" by auto
    then have min_p0:"min_call n \<Gamma> ((P0, s)#xs)"
      using min_call_seq_c1_not_finish[OF Seq(3) Seq(4) p0_cptn] ass by auto
    then have ex_xs:"\<exists>xs. min_call n \<Gamma> ((P0, s)#xs) \<and> (Q, t) # cfg1 = map (lift P1) xs" 
      using ass by auto
    then have min_xs:"min_call n \<Gamma> ((P0, s)#xs) \<and> (Q, t) # cfg1 = map (lift P1) xs" 
      using min_p0 ass by auto
    have "xs= (SOME xs. (min_call n \<Gamma> ((P0, s)#xs) \<and> (Q, t) # cfg1 = map (lift P1) xs))"
    proof -
      have "\<forall>xsa. min_call n \<Gamma> ((P0, s)#xsa) \<and> (Q, t) # cfg1 = map (lift P1) xsa \<longrightarrow> xsa = xs"
        using xs' ass by (metis map_lift_eq_xs_xs')
      thus ?thesis using min_xs some_equality by (metis (mono_tags, lifting))
    qed
    then have big:"biggest_nest_call P0 s ((Q', t) # xs') \<Gamma> n" 
      using biggest_nest_call.simps(1)[of P0 P1 s "((Q, t) # cfg1)" \<Gamma> n] 
            Seq(6) xs' ex_xs by auto         
    have reP0:"redex P0 = (Call f) \<and> \<Gamma> f = Some bdy \<and> 
              (\<exists>saa. s = Normal saa) \<and> t = s " using Seq(5) xs' by auto    
    have min_call:"min_call n \<Gamma> ((Q', t) # xs')" 
       using Seq(1)[OF min_p0 ctpn_P0 reP0] big xs' ass by auto
    thus ?thesis using min_call_seq_not_finish[OF min_call] ass xs' by blast
  next
    assume ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Skip \<and>
                  (\<exists>ys. (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
                  (Q, t) # cfg1 = map (lift P1) xs @ (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<or>
                fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and>
                  snd (last ((P0, s) # xs)) = Normal s' \<and>
                  s = Normal s'' \<and>
                  (\<exists>ys. (n, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call \<and>
                     (Q, t) # cfg1 = map (lift P1) xs @ (LanguageCon.com.Throw, Normal s') # ys)"
    {assume ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Skip \<and>
            (\<exists>ys. (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
            (Q, t) # cfg1 = map (lift P1) xs @ (P1, snd (((P0, s) # xs) ! length xs)) # ys)"     
     have ?thesis 
     proof (cases xs)
       case Nil thus ?thesis using Seq ass by fastforce
     next
       case (Cons xa xsa)
       then obtain ys where 
         seq2_ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Skip \<and> 
          (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
          (Q, t) # cfg1 = map (lift P1) (xa#xsa) @ (P1, snd (((P0, s) # xs) ! length xs)) # ys"
          using ass by auto 
        then obtain mq mp1 where 
         min_call_q:"min_call mq \<Gamma> ((P0, s) # xs)" and
         min_call_p1:"min_call mp1 \<Gamma> ((P1, snd (((P0, s) # xs) ! length xs)) # ys)"         
       using seq2_ass minimum_nest_call p0_cptn by fastforce               
       then have mp: "mq\<le>n \<and> mp1 \<le>n"
         using seq2_ass min_call_less_eq_n[of n \<Gamma> P0 s xs P1 ys  mq mp1] 
             Seq(3,4) p0_cptn by (simp add: last_length)
       have min_call:"min_call n \<Gamma> ((P0, s) # xs) \<or> 
             min_call n \<Gamma> ((P1, snd (((P0, s) # xs) ! length xs)) # ys)"
         using seq2_ass min_call_seq2[of n \<Gamma> P0 P1 s "(Q, t) # cfg1" xs ys] 
             Seq(3,4) p0_cptn by (simp add: last_length local.Cons)       
       from seq2_ass obtain Q' where Q':"Q=Seq Q' P1 \<and> xa=(Q',t)"          
       unfolding lift_def   
         by (metis (mono_tags, lifting) fst_conv length_greater_0_conv 
             list.simps(3) list.simps(9) nth_Cons_0 nth_append prod.case_eq_if prod.collapse snd_conv)  
       then have q'_n_cptn:"(n,\<Gamma>,(Q',t)#xsa)\<in>cptn_mod_nest_call" using p0_cptn Q' Cons
         using elim_cptn_mod_nest_call_n by blast 
       show ?thesis
       proof(cases "mp1=n")
         case True
         then have "min_call n \<Gamma> ((P1, snd (((P0, s) # xs) ! length xs)) # ys)"
           using min_call_p1 by auto
         then have min_P1:"min_call n \<Gamma> ((P1, snd ((xa # xsa) ! length xsa)) # ys)"
           using Cons seq2_ass by fastforce         
         then have p1_n_cptn:"(n, \<Gamma>,  (Q, t) # cfg1) \<in> cptn_mod_nest_call"
           using Seq.prems(1) Seq.prems(2) elim_cptn_mod_nest_call_n min_call_def by blast
         also then have "(\<forall>m<n. (m, \<Gamma>, (Q, t) # cfg1) \<notin> cptn_mod_nest_call)" 
         proof-
         { fix m
           assume ass:"m<n" 
           { assume Q_m:"(m, \<Gamma>, (Q, t) # cfg1) \<in> cptn_mod_nest_call"             
            then have False using min_P1 ass Q' Cons unfolding min_call_def
            proof -
              assume a1: "(n, \<Gamma>, (P1, snd ((xa # xsa) ! length xsa)) # ys) \<in> cptn_mod_nest_call \<and> (\<forall>m<n. (m, \<Gamma>, (P1, snd ((xa # xsa) ! length xsa)) # ys) \<notin> cptn_mod_nest_call)"
              have f2: "\<forall>n f ps. (n, f, ps) \<notin> cptn_mod_nest_call \<or> (\<forall>x c ca psa. ps \<noteq> (LanguageCon.com.Seq (c::('b, 'a, 'c,'d) LanguageCon.com) ca, x) # psa \<or> (\<exists>ps b ba. (n, f, (c, x) # ps) \<in> cptn_mod_nest_call \<and> seq_cond_nest psa ca ps c x ba b f n))"
                using div_seq_nest by blast
              have f3: "(P1, snd (last ((Q', t) # xsa))) # ys = (P1, snd (((P0, s) # xs) ! length xs)) # ys"
                by (simp add: Q' last_length local.Cons)
              have "fst (last ((Q', t) # xsa)) = LanguageCon.com.Skip"
                by (metis (no_types) Q' last_ConsR last_length list.distinct(1) local.Cons seq2_ass)
              then show ?thesis
                using f3 f2 a1 by (metis (no_types) Cons_lift_append Q' Seq_P_Ends_Normal Q_m ass seq2_ass)
            qed
           } 
         } then show ?thesis by auto
         qed           
         ultimately show ?thesis unfolding min_call_def by auto
       next
         case False
         then have "mp1<n" using mp by auto
         then have not_min_call_p1_n:"\<not> min_call n \<Gamma> ((P1, snd (last ((P0, s) # xs))) # ys)"
           using min_call_p1 last_length unfolding min_call_def by metis
         then have min_call:"min_call n \<Gamma> ((P0, s) # xs)" 
           using min_call last_length unfolding min_call_def by metis
         then have "(P0, s) # xs = (P0, s) # xa#xsa"
           using Cons by auto
         then have big:"biggest_nest_call P0 s (((Q',t))#xsa) \<Gamma> n"
         proof-
           have "\<not>(\<exists>xs. min_call n \<Gamma> ((P0, s)#xs) \<and> (Q, t) # cfg1 = map (lift P1) xs)"
             using min_call seq2_ass Cons
            proof -
              have "min_call n \<Gamma> ((LanguageCon.com.Seq P0 P1, s) # (Q, t) # cfg1)"
                using Seq.prems(1) Seq.prems(2) by blast
              then show ?thesis
                by (metis (no_types) Seq_P_Not_finish append_Nil2 list.simps(3) 
                          local.Cons min_call_def same_append_eq seq seq2_ass)
            qed
            moreover have "\<exists>xs ys. cond_seq_1 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys"
              using seq2_ass p0_cptn unfolding cond_seq_1_def 
              by (metis last_length local.Cons) 
            moreover have "(SOME xs. \<exists>ys. cond_seq_1 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys) = xs"  
            proof -
              let ?P = "\<lambda>xsa. \<exists>ys. (n, \<Gamma>, (P0, s) # xsa) \<in> cptn_mod_nest_call \<and>
                   fst (last ((P0, s) # xsa)) = LanguageCon.com.Skip \<and>
                   (n, \<Gamma>, (P1, snd (last ((P0, s) # xsa))) # ys) \<in> cptn_mod_nest_call \<and>
                   (Q, t) # cfg1 = map (lift P1) xsa @ (P1, snd (last ((P0, s) # xsa))) # ys"             
              have "(\<And>x. \<exists>ys. (n, \<Gamma>, (P0, s) # x) \<in> cptn_mod_nest_call \<and>
               fst (last ((P0, s) # x)) = LanguageCon.com.Skip \<and>
               (n, \<Gamma>, (P1, snd (last ((P0, s) # x))) # ys) \<in> cptn_mod_nest_call \<and>
               (Q, t) # cfg1 = map (lift P1) x @ (P1, snd (last ((P0, s) # x))) # ys \<Longrightarrow>
                   x = xs)"              
              by (metis Seq_P_Ends_Normal cptn_mod_nest_call.CptnModNestSeq2 seq)
              moreover have "\<exists>ys. (n, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call \<and>
                   fst (last ((P0, s) # xs)) = LanguageCon.com.Skip \<and>
                   (n, \<Gamma>, (P1, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
                   (Q, t) # cfg1 = map (lift P1) xs @ (P1, snd (last ((P0, s) # xs))) # ys"
                using ass  p0_cptn by (simp add: last_length)               
              ultimately show ?thesis using some_equality[of ?P xs]
                 unfolding cond_seq_1_def by blast 
            qed
            moreover have "(SOME ys. cond_seq_1 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys) = ys"
            proof -
               let ?P = "\<lambda>ys. (n, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call \<and>
                   fst (last ((P0, s) # xs)) = LanguageCon.com.Skip \<and>
                   (n, \<Gamma>, (P1, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
                   (Q, t) # cfg1 = map (lift P1) xs @ (P1, snd (last ((P0, s) # xs))) # ys"
                have "(n, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call \<and>
                   fst (last ((P0, s) # xs)) = LanguageCon.com.Skip \<and>
                   (n, \<Gamma>, (P1, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
                   (Q, t) # cfg1 = map (lift P1) xs @ (P1, snd (last ((P0, s) # xs))) # ys"
                 using p0_cptn seq2_ass Cons   by (simp add: last_length) 
                then show ?thesis using some_equality[of ?P ys]
                 unfolding cond_seq_1_def by fastforce      
            qed
            ultimately have "biggest_nest_call P0 s xs \<Gamma> n"
              using not_min_call_p1_n Seq(6) 
                    biggest_nest_call.simps(1)[of P0 P1 s "(Q, t) # cfg1" \<Gamma> n]
              by presburger
            then show ?thesis  using Cons Q' by auto
          qed
          have C:"(P0, s) # xs = (P0, s) # (Q', t) # xsa" using Cons Q' by auto
          have reP0:"redex P0 = (Call f) \<and> \<Gamma> f = Some bdy \<and> 
            (\<exists>saa. s = Normal saa) \<and> t = s" using Seq(5) Q' by auto
          then have min_call:"min_call n \<Gamma> ((Q', t) # xsa)" using Seq(1)[OF min_call C reP0 big]
            by auto
          have p1_n_cptn:"(n, \<Gamma>,  (Q, t) # cfg1) \<in> cptn_mod_nest_call"
            using Seq.prems(1) Seq.prems(2) elim_cptn_mod_nest_call_n min_call_def by blast
          also then have "(\<forall>m<n. (m, \<Gamma>, (Q, t) # cfg1) \<notin> cptn_mod_nest_call)" 
          proof-
           { fix m
             assume ass:"m<n" 
             { assume Q_m:"(m, \<Gamma>, (Q, t) # cfg1) \<in> cptn_mod_nest_call" 
               then obtain xsa' s1 s1' where 
                  p0_cptn:"(m, \<Gamma>,(Q', t)#xsa') \<in> cptn_mod_nest_call"  and
                  seq:"seq_cond_nest cfg1 P1 xsa' Q' t s1 s1' \<Gamma> m"
               using div_seq_nest[of m \<Gamma> "(Q, t) # cfg1"] Q' by blast
               then have "xsa=xsa'" 
                 using seq2_ass 
                 Seq_P_Ends_Normal[of cfg1 P1 xsa Q' t ys m \<Gamma> xsa' s1 s1'] Cons
                 by (metis Cons_lift_append Q' Q_m last.simps last_length list.inject list.simps(3)) 
               then have False using min_call p0_cptn ass unfolding min_call_def by auto 
             } 
           } then show ?thesis by auto qed
             
         ultimately show ?thesis unfolding min_call_def by auto
       qed    
     qed
    }note l=this
    {assume ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and>
             snd (last ((P0, s) # xs)) = Normal s' \<and>
            s = Normal s'' \<and> (\<exists>ys. (n, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call \<and>
          (Q, t) # cfg1 = map (lift P1) xs @ (LanguageCon.com.Throw, Normal s') # ys)"          
     have ?thesis
     proof (cases "\<Gamma>\<turnstile>\<^sub>c(LanguageCon.com.Seq P0 P1, s) \<rightarrow> (Q,t)")
       case True 
       thus  ?thesis
       proof (cases xs)
          case Nil thus ?thesis using Seq ass by fastforce
       next
         case (Cons xa xsa)
         then obtain ys where 
           seq2_ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and>
             snd (last ((P0, s) # xs)) = Normal s' \<and>
            s = Normal s'' \<and>  (n, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call \<and>
           (Q, t) # cfg1 = map (lift P1) xs @ (LanguageCon.com.Throw, Normal s') # ys"
            using ass by auto 
         then have t_eq:"t=Normal s''" using Seq by fastforce
         obtain mq mp1 where 
           min_call_q:"min_call mq \<Gamma> ((P0, s) # xs)" and
           min_call_p1:"min_call mp1 \<Gamma> ((Throw, snd (((P0, s) # xs) ! length xs)) # ys)"         
         using seq2_ass minimum_nest_call p0_cptn by (metis last_length)
         then have mp1_zero:"mp1=0" by (simp add: throw_min_nested_call_0)
         then have min_call: "min_call n \<Gamma> ((P0, s) # xs)"  
           using seq2_ass min_call_seq3[of n \<Gamma> P0 P1 s "(Q, t) # cfg1" s'' xs s' ys]
             Seq(3,4) p0_cptn by (metis last_length)      
         have n_z:"n>0" using redex_call_cptn_mod_min_nest_call_gr_zero[OF Seq(3) Seq(4) Seq(5) True]
           by auto          
         from seq2_ass obtain Q' where Q':"Q=Seq Q' P1 \<and> xa=(Q',t)"          
           unfolding lift_def using Cons
          proof -
            assume a1: "\<And>Q'. Q = LanguageCon.com.Seq Q' P1 \<and> xa = (Q', t) \<Longrightarrow> thesis"
            have "(LanguageCon.com.Seq (fst xa) P1, snd xa) = ((Q, t) # cfg1) ! 0"
             using seq2_ass unfolding lift_def
              by (simp add: Cons case_prod_unfold)
            then show ?thesis
              using a1 by fastforce
          qed  
         have big_call:"biggest_nest_call P0 s ((Q',t)#xsa) \<Gamma> n"
         proof-
           have "\<not>(\<exists>xs. min_call n \<Gamma> ((P0, s)#xs) \<and> (Q, t) # cfg1 = map (lift P1) xs)"
             using min_call seq2_ass Cons Seq.prems(1) Seq.prems(2)
           by (metis Seq_P_Not_finish append_Nil2 list.simps(3) min_call_def same_append_eq seq)
           moreover have "\<not>(\<exists>xs ys. cond_seq_1 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys)" 
             using min_call seq2_ass p0_cptn Cons Seq.prems(1) Seq.prems(2) 
             unfolding cond_seq_1_def
            by (metis com.distinct(17) com.distinct(71) last_length 
                      map_lift_some_eq seq_and_if_not_eq(4))
           moreover have "(SOME xs. \<exists>ys s' s''. cond_seq_2 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys s' s'') = xs"
           proof-
             let ?P="\<lambda>xsa. \<exists>ys s' s''. s= Normal s'' \<and> 
                    (n,\<Gamma>, (P0, s)#xs) \<in> cptn_mod_nest_call \<and> 
                    fst(last ((P0, s)#xs)) = Throw \<and>
                    snd(last ((P0, s)#xs)) = Normal s' \<and> 
                    (n,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call \<and> 
                     ((Q, t) # cfg1)=(map (lift P1) xs)@((Throw,Normal s')#ys)"
             have "(\<And>x. \<exists>ys s' s''. s= Normal s'' \<and> 
                    (n,\<Gamma>, (P0, s)#x) \<in> cptn_mod_nest_call \<and> 
                    fst(last ((P0, s)#x)) = Throw \<and>
                    snd(last ((P0, s)#x)) = Normal s' \<and> 
                    (n,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call \<and> 
                     ((Q, t) # cfg1)=(map (lift P1) x)@((Throw,Normal s')#ys) \<Longrightarrow>
                    x=xs)" using map_lift_some_eq seq2_ass by fastforce
             moreover have "\<exists>ys s' s''. s= Normal s'' \<and> 
                    (n,\<Gamma>, (P0, s)#xs) \<in> cptn_mod_nest_call \<and> 
                    fst(last ((P0, s)#xs)) = Throw \<and>
                    snd(last ((P0, s)#xs)) = Normal s' \<and> 
                    (n,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call \<and> 
                     ((Q, t) # cfg1)=(map (lift P1) xs)@((Throw,Normal s')#ys)" 
                using ass p0_cptn by (simp add: last_length Cons)
            ultimately show ?thesis using some_equality[of ?P xs]
                 unfolding cond_seq_2_def by blast
         qed
           ultimately have "biggest_nest_call P0 s xs \<Gamma> n"
            using  Seq(6) 
                  biggest_nest_call.simps(1)[of P0 P1 s "(Q, t) # cfg1" \<Gamma> n]
            by presburger
           then show ?thesis  using Cons Q' by auto
         qed         
         have min_call:"min_call n \<Gamma> ((Q',t)#xsa)" 
           using Seq(1)[OF min_call _ _ big_call] Seq(5) Cons Q' by fastforce   
         then have p1_n_cptn:"(n, \<Gamma>,  (Q, t) # cfg1) \<in> cptn_mod_nest_call"
            using Seq.prems(1) Seq.prems(2) elim_cptn_mod_nest_call_n min_call_def by blast   
         also then have "(\<forall>m<n. (m, \<Gamma>, (Q, t) # cfg1) \<notin> cptn_mod_nest_call)" 
          proof-
           { fix m
             assume ass:"m<n" 
             { assume Q_m:"(m, \<Gamma>, (Q, t) # cfg1) \<in> cptn_mod_nest_call" 
               then obtain xsa' s1 s1' where 
                  p0_cptn:"(m, \<Gamma>,(Q', t)#xsa') \<in> cptn_mod_nest_call"  and
                  seq:"seq_cond_nest cfg1 P1 xsa' Q' (Normal s'') s1 s1' \<Gamma> m"
               using div_seq_nest[of m \<Gamma> "(Q, t) # cfg1"] Q' t_eq by blast
               then have "xsa=xsa'" 
                 using seq2_ass 
                 Seq_P_Ends_Abort[of cfg1 P1 xsa s' ys Q' s'' m \<Gamma> xsa' s1 s1' ] Cons Q' Q_m
                 by (simp add: Cons_lift_append last_length t_eq)                 
               then have False using min_call p0_cptn ass unfolding min_call_def by auto 
             } 
           } then show ?thesis by auto qed          
         ultimately show ?thesis unfolding min_call_def by auto
       qed
     next
       case False 
       then have env:"\<Gamma>\<turnstile>\<^sub>c(LanguageCon.com.Seq P0 P1, s) \<rightarrow>\<^sub>e (Q,t)" using Seq
         by (meson elim_cptn_mod_nest_step_c min_call_def)
       moreover then have Q:"Q=Seq P0 P1" using env_c_c' by blast        
       ultimately show ?thesis using Seq
        proof -
          obtain nn :: "(('b, 'a, 'c,'d) LanguageCon.com \<times> ('b, 'c) xstate) list \<Rightarrow> 
                         ('a \<Rightarrow> ('b, 'a, 'c,'d) LanguageCon.com option) \<Rightarrow> nat \<Rightarrow> nat" where
            f1: "\<forall>x0 x1 x2. (\<exists>v3<x2. (v3, x1, x0) \<in> cptn_mod_nest_call) = (nn x0 x1 x2 < x2 \<and> (nn x0 x1 x2, x1, x0) \<in> cptn_mod_nest_call)"
            by moura
          have f2: "(n, \<Gamma>, (LanguageCon.com.Seq P0 P1, s) # (Q, t) # cfg1) \<in> cptn_mod_nest_call \<and> (\<forall>n. \<not> n < n \<or> (n, \<Gamma>, (LanguageCon.com.Seq P0 P1, s) # (Q, t) # cfg1) \<notin> cptn_mod_nest_call)"
            using local.Seq(3) local.Seq(4) min_call_def by blast
          then have "\<not> nn ((Q, t) # cfg1) \<Gamma> n < n \<or> (nn ((Q, t) # cfg1) \<Gamma> n, \<Gamma>, (Q, t) # cfg1) \<notin> cptn_mod_nest_call"
            using False env env_c_c'  not_func_redex_cptn_mod_nest_n_env 
            by (metis Seq.prems(1) Seq.prems(2) min_call_def)
          then show ?thesis
            using f2 f1 by (meson elim_cptn_mod_nest_call_n min_call_def)
        qed
     qed          
    }
    thus ?thesis using l ass by fastforce
  qed
next
  case (Catch P0 P1) 
then obtain xs s' s'' where 
          p0_cptn:"(n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call"  and 
          catch:"catch_cond_nest ((Q,t)#cfg1) P1 xs P0 s s'' s' \<Gamma> n"
  using div_catch_nest[of n \<Gamma> cfg] unfolding min_call_def by blast
  
  show ?case using catch unfolding catch_cond_nest_def 
  proof
    assume ass:"(Q, t) # cfg1 = map (lift_catch P1) xs"   
    then obtain Q' xs' where xs':"Q=Catch Q' P1 \<and> xs=(Q',t)#xs'"
      unfolding lift_catch_def by fastforce
    then have ctpn_P0:"(P0, s) # xs = (P0, s) # (Q', t) # xs'" by auto
    then have min_p0:"min_call n \<Gamma> ((P0, s)#xs)"
      using min_call_catch_c1_not_finish[OF Catch(3) Catch(4) p0_cptn] ass by auto
    then have ex_xs:"\<exists>xs. min_call n \<Gamma> ((P0, s)#xs) \<and> (Q, t) # cfg1 = map (lift_catch P1) xs" 
      using ass by auto
    then have min_xs:"min_call n \<Gamma> ((P0, s)#xs) \<and> (Q, t) # cfg1 = map (lift_catch P1) xs" 
      using min_p0 ass by auto
    have "xs= (SOME xs. (min_call n \<Gamma> ((P0, s)#xs) \<and> (Q, t) # cfg1 = map (lift_catch P1) xs))"
    proof -
      have "\<forall>xsa. min_call n \<Gamma> ((P0, s)#xsa) \<and> (Q, t) # cfg1 = map (lift_catch P1) xsa \<longrightarrow> xsa = xs"
        using xs' ass by (metis map_lift_catch_eq_xs_xs')
      thus ?thesis using min_xs some_equality by (metis (mono_tags, lifting))
    qed
    then have big:"biggest_nest_call P0 s ((Q', t) # xs') \<Gamma> n" 
      using biggest_nest_call.simps(2)[of P0 P1 s "((Q, t) # cfg1)" \<Gamma> n] 
            Catch(6) xs' ex_xs by auto          
    have reP0:"redex P0 = (Call f) \<and> \<Gamma> f = Some bdy \<and> 
              (\<exists>saa. s = Normal saa) \<and> t = s " using Catch(5) xs' by auto    
    have min_call:"min_call n \<Gamma> ((Q', t) # xs')" 
       using Catch(1)[OF min_p0 ctpn_P0 reP0] big xs' ass by auto
    thus ?thesis using min_call_catch_not_finish[OF min_call] ass xs' by blast
  next
    assume ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and>
                snd (last ((P0, s) # xs)) = Normal s' \<and>
                s = Normal s'' \<and>
               (\<exists>ys. (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
                  (Q, t) # cfg1 = map (lift_catch P1) xs @ (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<or>
                   fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Skip \<and>
                  (\<exists>ys. (n, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
                (Q, t) # cfg1 = map (lift_catch P1) xs @ (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys)" 
    {assume ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and>
                snd (last ((P0, s) # xs)) = Normal s' \<and>
                s = Normal s'' \<and>
               (\<exists>ys. (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
                  (Q, t) # cfg1 = map (lift_catch P1) xs @ (P1, snd (((P0, s) # xs) ! length xs)) # ys)"     
     have ?thesis 
     proof (cases xs)
       case Nil thus ?thesis using Catch ass by fastforce
     next
       case (Cons xa xsa)
       then obtain ys where 
         catch2_ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and>
                snd (last ((P0, s) # xs)) = Normal s' \<and>
                s = Normal s'' \<and>
                (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
                (Q, t) # cfg1 = map (lift_catch P1) xs @ (P1, snd (((P0, s) # xs) ! length xs)) # ys"
          using ass by auto 
        then obtain mq mp1 where 
         min_call_q:"min_call mq \<Gamma> ((P0, s) # xs)" and
         min_call_p1:"min_call mp1 \<Gamma> ((P1, snd (((P0, s) # xs) ! length xs)) # ys)"         
       using catch2_ass minimum_nest_call p0_cptn by fastforce               
       then have mp: "mq\<le>n \<and> mp1 \<le>n"
         using catch2_ass min_call_less_eq_n 
             Catch(3,4) p0_cptn by (metis last_length) 
       have min_call:"min_call n \<Gamma> ((P0, s) # xs) \<or> 
             min_call n \<Gamma> ((P1, snd (((P0, s) # xs) ! length xs)) # ys)"
         using catch2_ass min_call_catch3[of n \<Gamma> P0 P1 s'' "(Q, t) # cfg1" xs s' ys] 
             Catch(3,4) p0_cptn by (metis last_length)       
       from catch2_ass obtain Q' where Q':"Q=Catch Q' P1 \<and> xa=(Q',t)"          
       unfolding lift_catch_def
        proof -
          assume a1: "\<And>Q'. Q = LanguageCon.com.Catch Q' P1 \<and> xa = (Q', t) \<Longrightarrow> thesis"
          assume "fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and> snd (last ((P0, s) # xs)) = Normal s' \<and> s = Normal s'' \<and> (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and> (Q, t) # cfg1 = map (\<lambda>(P, s). (LanguageCon.com.Catch P P1, s)) xs @ (P1, snd (((P0, s) # xs) ! length xs)) # ys"
          then have "(LanguageCon.com.Catch (fst xa) P1, snd xa) = ((Q, t) # cfg1) ! 0"
            by (simp add: local.Cons prod.case_eq_if)
          then show ?thesis
            using a1 by force
        qed            
       then have q'_n_cptn:"(n,\<Gamma>,(Q',t)#xsa)\<in>cptn_mod_nest_call" using p0_cptn Q' Cons
         using elim_cptn_mod_nest_call_n by blast 
       show ?thesis
       proof(cases "mp1=n")
         case True
         then have "min_call n \<Gamma> ((P1, snd (((P0, s) # xs) ! length xs)) # ys)"
           using min_call_p1 by auto
         then have min_P1:"min_call n \<Gamma> ((P1, snd ((xa # xsa) ! length xsa)) # ys)"
           using Cons catch2_ass by fastforce         
         then have p1_n_cptn:"(n, \<Gamma>,  (Q, t) # cfg1) \<in> cptn_mod_nest_call"
           using Catch.prems(1) Catch.prems(2) elim_cptn_mod_nest_call_n min_call_def by blast
         also then have "(\<forall>m<n. (m, \<Gamma>, (Q, t) # cfg1) \<notin> cptn_mod_nest_call)" 
         proof-
         { fix m
           assume ass:"m<n" 
           { assume Q_m:"(m, \<Gamma>, (Q, t) # cfg1) \<in> cptn_mod_nest_call"   
             then have t_eq_s:"t=Normal s''" using Catch catch2_ass by fastforce                      
            then obtain xsa' s1 s1' where 
                  p0_cptn:"(m, \<Gamma>,(Q', t)#xsa') \<in> cptn_mod_nest_call"  and
                  catch_cond:"catch_cond_nest cfg1 P1 xsa' Q' (Normal s'') s1 s1' \<Gamma> m"
              using Q_m div_catch_nest[of m \<Gamma> "(Q, t) # cfg1"] Q' by blast
            have fst:"fst (last ((Q', Normal s'') # xsa)) = LanguageCon.com.Throw" 
              using catch2_ass Cons Q' by (simp add: last_length  t_eq_s)
            have cfg:"cfg1 = map (lift_catch P1) xsa @ (P1, snd (last ((Q', Normal s'') # xsa))) # ys"
              using catch2_ass Cons Q' by (simp add: last_length  t_eq_s)
            have snd:"snd (last ((Q', Normal s'') # xsa)) = Normal s'"
              using catch2_ass Cons Q' by (simp add: last_length  t_eq_s)
            then have "xsa=xsa' \<and> 
                   (m, \<Gamma>, (P1, snd (((Q', Normal s'') # xsa) ! length xsa)) # ys) \<in> cptn_mod_nest_call" 
              using catch2_ass Catch_P_Ends_Normal[OF cfg fst snd catch_cond] Cons
              by auto 
            then have False using min_P1 ass Q' t_eq_s unfolding min_call_def by auto              
           } 
         } then show ?thesis by auto
         qed           
         ultimately show ?thesis unfolding min_call_def by auto
       next
         case False
         then have "mp1<n" using mp by auto
         then have not_min_call_p1_n:"\<not> min_call n \<Gamma> ((P1, snd (last ((P0, s) # xs))) # ys)"
           using min_call_p1 last_length unfolding min_call_def by metis
         then have min_call:"min_call n \<Gamma> ((P0, s) # xs)" 
           using min_call last_length unfolding min_call_def by metis
         then have "(P0, s) # xs = (P0, s) # xa#xsa"
           using Cons by auto
         then have big:"biggest_nest_call P0 s (((Q',t))#xsa) \<Gamma> n"
         proof-
           have "\<not>(\<exists>xs. min_call n \<Gamma> ((P0, s)#xs) \<and> (Q, t) # cfg1 = map (lift_catch P1) xs)"
             using min_call catch2_ass Cons
            proof -
              have "min_call n \<Gamma> ((Catch P0 P1, s) # (Q, t) # cfg1)"
                using Catch.prems(1) Catch.prems(2) by blast
              then show ?thesis
                by (metis (no_types) Catch_P_Not_finish append_Nil2 list.simps(3) 
                     same_append_eq catch catch2_ass)
            qed
            moreover have "\<not>(\<exists>xs ys. cond_catch_1 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys)"
              unfolding cond_catch_1_def using catch2_ass 
              by (metis Catch_P_Ends_Skip LanguageCon.com.distinct(17) catch last_length)
            moreover have "\<exists>xs ys. cond_catch_2 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys s' s''"
              using catch2_ass p0_cptn unfolding cond_catch_2_def last_length
              by metis 
            moreover have "(SOME xs. \<exists>ys s' s''. cond_catch_2 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys s' s'') = xs"  
            proof -
              let ?P = "\<lambda>xsa. s = Normal s'' \<and>
                              (n, \<Gamma>, (P0, s) # xsa) \<in> cptn_mod_nest_call \<and>
                              fst (last ((P0, s) # xsa)) = LanguageCon.com.Throw \<and>
                              snd (last ((P0, s) # xsa)) = Normal s' \<and>
                               (n, \<Gamma>, (P1, Normal s') # ys) \<in> cptn_mod_nest_call \<and> 
                               (Q, t) # cfg1 = map (lift_catch P1) xsa @ (P1, Normal s') # ys"             
              have "(\<And>x. \<exists>ys s' s''. s = Normal s'' \<and>
                              (n, \<Gamma>, (P0, s) # x) \<in> cptn_mod_nest_call \<and>
                              fst (last ((P0, s) # x)) = LanguageCon.com.Throw \<and>
                              snd (last ((P0, s) # x)) = Normal s' \<and>
                               (n, \<Gamma>, (P1, Normal s') # ys) \<in> cptn_mod_nest_call \<and> 
                               (Q, t) # cfg1 = map (lift_catch P1) x @ (P1, Normal s') # ys \<Longrightarrow>
                   x = xs)"              
              by (metis Catch_P_Ends_Normal catch)
              moreover have "\<exists>ys. s = Normal s'' \<and>
                              (n, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call \<and>
                              fst (last ((P0, s) # xs)) = LanguageCon.com.Throw \<and>
                              snd (last ((P0, s) # xs)) = Normal s' \<and>
                               (n, \<Gamma>, (P1, Normal s') # ys) \<in> cptn_mod_nest_call \<and> 
                               (Q, t) # cfg1 = map (lift_catch P1) xs @ (P1, Normal s') # ys"
                using ass  p0_cptn   by (metis (full_types) last_length )             
              ultimately show ?thesis using some_equality[of ?P xs]
                 unfolding cond_catch_2_def by blast 
            qed
            moreover have "(SOME ys. \<exists>s' s''. cond_catch_2 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys s' s'') = ys"
            proof -
               let ?P = "\<lambda>ysa. s = Normal s'' \<and>
                              (n, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call \<and>
                              fst (last ((P0, s) # xs)) = LanguageCon.com.Throw \<and>
                              snd (last ((P0, s) # xs)) = Normal s' \<and>
                               (n, \<Gamma>, (P1, Normal s') # ysa) \<in> cptn_mod_nest_call \<and> 
                               (Q, t) # cfg1 = map (lift_catch P1) xs @ (P1, Normal s') # ysa"
                have "(\<And>x.  \<exists>s' s''. s = Normal s'' \<and>
                          (n, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call \<and>
                          fst (last ((P0, s) # xs)) = LanguageCon.com.Throw \<and>
                          snd (last ((P0, s) # xs)) = Normal s' \<and>
                          (n, \<Gamma>, (P1, Normal s') # x) \<in> cptn_mod_nest_call \<and> (Q, t) # cfg1 = map (lift_catch P1) xs @ (P1, Normal s') # x \<Longrightarrow>
                          x = ys)" using catch2_ass by auto 
                moreover have "s = Normal s'' \<and>
                      (n, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call \<and>
                       fst (last ((P0, s) # xs)) = LanguageCon.com.Throw \<and>
                       snd (last ((P0, s) # xs)) = Normal s' \<and>
                      (n, \<Gamma>, (P1, Normal s') # ys) \<in> cptn_mod_nest_call \<and> 
                       (Q, t) # cfg1 = map (lift_catch P1) xs @ (P1, Normal s') # ys"
                using ass  p0_cptn by (metis (full_types) catch2_ass last_length p0_cptn)             
                ultimately show ?thesis using some_equality[of ?P ys]
                 unfolding cond_catch_2_def by blast
            qed            
            ultimately have "biggest_nest_call P0 s xs \<Gamma> n"
              using not_min_call_p1_n Catch(6) 
                    biggest_nest_call.simps(2)[of P0 P1 s "(Q, t) # cfg1" \<Gamma> n]
              by presburger
            then show ?thesis  using Cons Q' by auto
          qed
          have C:"(P0, s) # xs = (P0, s) # (Q', t) # xsa" using Cons Q' by auto
          have reP0:"redex P0 = (Call f) \<and> \<Gamma> f = Some bdy \<and> 
            (\<exists>saa. s = Normal saa) \<and> t = s " using Catch(5) Q' by auto
          then have min_call:"min_call n \<Gamma> ((Q', t) # xsa)" using Catch(1)[OF min_call C reP0 big]
            by auto
          have p1_n_cptn:"(n, \<Gamma>,  (Q, t) # cfg1) \<in> cptn_mod_nest_call"
            using Catch.prems(1) Catch.prems(2) elim_cptn_mod_nest_call_n min_call_def by blast
          also then have "(\<forall>m<n. (m, \<Gamma>, (Q, t) # cfg1) \<notin> cptn_mod_nest_call)" 
          proof-
           { fix m
             assume ass:"m<n" 
             { assume Q_m:"(m, \<Gamma>, (Q, t) # cfg1) \<in> cptn_mod_nest_call" 
               then have t_eq_s:"t=Normal s''" using Catch catch2_ass by fastforce
               then obtain xsa' s1 s1' where 
                  p0_cptn:"(m, \<Gamma>,(Q', t)#xsa') \<in> cptn_mod_nest_call"  and
                  catch_cond:"catch_cond_nest cfg1 P1 xsa' Q' (Normal s'') s1 s1' \<Gamma> m"
               using Q_m div_catch_nest[of m \<Gamma> "(Q, t) # cfg1"] Q' by blast
               have fst:"fst (last ((Q', Normal s'') # xsa)) = LanguageCon.com.Throw" 
                 using catch2_ass Cons Q' by (simp add: last_length  t_eq_s)
              have cfg:"cfg1 = map (lift_catch P1) xsa @ (P1, snd (last ((Q', Normal s'') # xsa))) # ys"
                 using catch2_ass Cons Q' by (simp add: last_length  t_eq_s)
              have snd:"snd (last ((Q', Normal s'') # xsa)) = Normal s'"
                using catch2_ass Cons Q' by (simp add: last_length  t_eq_s)
               then have "xsa=xsa'" 
                 using catch2_ass Catch_P_Ends_Normal[OF cfg fst snd catch_cond] Cons
                 by auto 
               then have False using min_call p0_cptn ass unfolding min_call_def by auto 
             } 
           } then show ?thesis by auto qed
         ultimately show ?thesis unfolding min_call_def by auto
       qed    
     qed
    }note l=this
    {assume ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Skip \<and>
             (\<exists>ys. (n, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
             (Q, t) # cfg1 = map (lift_catch P1) xs @ (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys)"
     have ?thesis
     proof (cases "\<Gamma>\<turnstile>\<^sub>c(Catch P0 P1, s) \<rightarrow> (Q,t)")
       case True 
       thus  ?thesis
       proof (cases xs)
          case Nil thus ?thesis using Catch ass by fastforce
       next
         case (Cons xa xsa)
         then obtain ys where 
           catch2_ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Skip \<and>
             (n, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
             (Q, t) # cfg1 = map (lift_catch P1) xs @ (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys"
            using ass by auto 
         then have t_eq:"t=s" using Catch by fastforce
         obtain mq mp1 where 
           min_call_q:"min_call mq \<Gamma> ((P0, s) # xs)" and
           min_call_p1:"min_call mp1 \<Gamma> ((Skip, snd (((P0, s) # xs) ! length xs)) # ys)"         
         using catch2_ass minimum_nest_call p0_cptn by (metis last_length)
         then have mp1_zero:"mp1=0" by (simp add: skip_min_nested_call_0)
         then have min_call: "min_call n \<Gamma> ((P0, s) # xs)"  
           using catch2_ass min_call_catch2[of n \<Gamma> P0 P1 s "(Q, t) # cfg1" xs ys]
             Catch(3,4) p0_cptn by (metis last_length)      
         have n_z:"n>0" using redex_call_cptn_mod_min_nest_call_gr_zero[OF Catch(3) Catch(4) Catch(5) True]
           by auto          
         from catch2_ass obtain Q' where Q':"Q=Catch Q' P1 \<and> xa=(Q',t)"          
           unfolding lift_catch_def using Cons
          proof -
            assume a1: "\<And>Q'. Q = Catch Q' P1 \<and> xa = (Q', t) \<Longrightarrow> thesis"
            have "(Catch (fst xa) P1, snd xa) = ((Q, t) # cfg1) ! 0"
             using catch2_ass unfolding lift_catch_def
              by (simp add: Cons case_prod_unfold)
            then show ?thesis
              using a1 by fastforce
          qed  
         have big_call:"biggest_nest_call P0 s ((Q',t)#xsa) \<Gamma> n"
         proof-
           have "\<not>(\<exists>xs. min_call n \<Gamma> ((P0, s)#xs) \<and> (Q, t) # cfg1 = map (lift_catch P1) xs)"
             using min_call catch2_ass Cons
           proof -
             have "min_call n \<Gamma> ((Catch P0 P1, s) # (Q, t) # cfg1)"
               using Catch.prems(1) Catch.prems(2) by blast
             then show ?thesis
               by (metis (no_types) Catch_P_Not_finish append_Nil2 list.simps(3) 
                     same_append_eq catch catch2_ass)
           qed
           moreover have "(\<exists>xs ys. cond_catch_1 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys)"
             using catch2_ass p0_cptn unfolding cond_catch_1_def last_length
             by metis
           moreover have "(SOME xs. \<exists>ys. cond_catch_1 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys) = xs"
           proof -
             let ?P = "\<lambda>xsa. \<exists>ys. (n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call \<and> 
                            fst (last ((P0, s) # xs)) = LanguageCon.com.Skip \<and>
                             (n, \<Gamma>, (LanguageCon.com.Skip, 
                                snd (last ((P0, s) # xsa))) # ys) \<in> cptn_mod_nest_call \<and>
                             (Q, t) # cfg1 = map (lift_catch P1) xsa @ 
                               (LanguageCon.com.Skip, snd (last ((P0, s) # xsa))) # ys"
             have "\<And>xsa. \<exists>ys. (n, \<Gamma>,(P0, s)#xsa) \<in> cptn_mod_nest_call \<and> 
                             fst (last ((P0, s) # xs)) = LanguageCon.com.Skip \<and>
                             (n, \<Gamma>, (LanguageCon.com.Skip, 
                                snd (last ((P0, s) # xsa))) # ys) \<in> cptn_mod_nest_call \<and>
                             (Q, t) # cfg1 = map (lift_catch P1) xsa @ 
                               (LanguageCon.com.Skip, snd (last ((P0, s) # xsa))) # ys \<Longrightarrow>
                           xsa = xs"
             using Catch_P_Ends_Skip catch  catch2_ass map_lift_catch_some_eq by fastforce  
             moreover have "\<exists>ys. (n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call \<and>
                               fst (last ((P0, s) # xs)) = LanguageCon.com.Skip \<and>
                             (n, \<Gamma>, (LanguageCon.com.Skip, 
                                snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
                             (Q, t) # cfg1 = map (lift_catch P1) xs @ 
                               (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys" 
               using ass p0_cptn by (simp add: last_length) 
             ultimately show ?thesis using some_equality[of ?P xs]
                 unfolding cond_catch_1_def by blast 
           qed           
           ultimately have "biggest_nest_call P0 s xs \<Gamma> n"
            using  Catch(6) 
                  biggest_nest_call.simps(2)[of P0 P1 s "(Q, t) # cfg1" \<Gamma> n]
            by presburger
           then show ?thesis  using Cons Q' by auto
         qed         
         have min_call:"min_call n \<Gamma> ((Q',t)#xsa)" 
           using Catch(1)[OF min_call _ _  big_call] Catch(5) Cons Q' by fastforce   
         then have p1_n_cptn:"(n, \<Gamma>,  (Q, t) # cfg1) \<in> cptn_mod_nest_call"
            using Catch.prems(1) Catch.prems(2) elim_cptn_mod_nest_call_n min_call_def by blast   
         also then have "(\<forall>m<n. (m, \<Gamma>, (Q, t) # cfg1) \<notin> cptn_mod_nest_call)" 
          proof-
           { fix m
             assume ass:"m<n" 
             { assume Q_m:"(m, \<Gamma>, (Q, t) # cfg1) \<in> cptn_mod_nest_call" 
               then obtain xsa' s1 s1' where 
                  p0_cptn:"(m, \<Gamma>,(Q', t)#xsa') \<in> cptn_mod_nest_call"  and
                  seq:"catch_cond_nest cfg1 P1 xsa' Q' t s1 s1' \<Gamma> m"
               using div_catch_nest[of m \<Gamma> "(Q, t) # cfg1"] Q' t_eq by blast
               then have "xsa=xsa'" 
                 using catch2_ass 
                 Catch_P_Ends_Skip[of cfg1 P1 xsa Q' t ys xsa' s1 s1']  
                 Cons Q' Q_m 
                 by (simp add:  last_length)                 
               then have False using min_call p0_cptn ass unfolding min_call_def by auto 
             } 
           } then show ?thesis by auto qed          
         ultimately show ?thesis unfolding min_call_def by auto
       qed
     next
       case False 
       then have env:"\<Gamma>\<turnstile>\<^sub>c(Catch P0 P1, s) \<rightarrow>\<^sub>e (Q,t)" using Catch
         by (meson elim_cptn_mod_nest_step_c min_call_def)
       moreover then have Q:"Q=Catch P0 P1" using env_c_c' by blast        
       ultimately show ?thesis using Catch
        proof -
          obtain nn :: "(('b, 'a, 'c,'d) LanguageCon.com \<times> ('b, 'c) xstate) list \<Rightarrow> ('a \<Rightarrow> ('b, 'a, 'c,'d) LanguageCon.com option) \<Rightarrow> nat \<Rightarrow> nat" where
            f1: "\<forall>x0 x1 x2. (\<exists>v3<x2. (v3, x1, x0) \<in> cptn_mod_nest_call) = (nn x0 x1 x2 < x2 \<and> (nn x0 x1 x2, x1, x0) \<in> cptn_mod_nest_call)"
            by moura
          have f2: "(n, \<Gamma>, (LanguageCon.com.Catch P0 P1, s) # (Q, t) # cfg1) \<in> cptn_mod_nest_call \<and> (\<forall>n. \<not> n < n \<or> (n, \<Gamma>, (LanguageCon.com.Catch P0 P1, s) # (Q, t) # cfg1) \<notin> cptn_mod_nest_call)"
            using local.Catch(3) local.Catch(4) min_call_def by blast
          then have "\<not> nn ((Q, t) # cfg1) \<Gamma> n < n \<or> (nn ((Q, t) # cfg1) \<Gamma> n, \<Gamma>, (Q, t) # cfg1) \<notin> cptn_mod_nest_call"
            using False env env_c_c'  not_func_redex_cptn_mod_nest_n_env 
            by (metis Catch.prems(1) Catch.prems(2) min_call_def)
          then show ?thesis
            using f2 f1 by (meson elim_cptn_mod_nest_call_n min_call_def)
        qed
     qed   
    }
    thus ?thesis using l ass by fastforce
  qed   
qed (fastforce)+


lemma cptn_mod_nest_n_1:
  assumes a0:"(n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call" and
          a1:"cfs=(p,s)#cfs'" and
          a2:"\<not> (min_call n \<Gamma> cfs)"
  shows "(n-1,\<Gamma>,cfs) \<in>  cptn_mod_nest_call"
using a0 a1 a2 
by (metis (no_types, lifting) Suc_diff_1 Suc_leI cptn_mod_nest_mono less_nat_zero_code min_call_def not_less)

lemma cptn_mod_nest_tl_n_1:
  assumes a0:"(n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call" and
          a1:"cfs=(p,s)#(q,t)#cfs'" and
          a2:"\<not> (min_call n \<Gamma> cfs)"
  shows "(n-1,\<Gamma>,(q,t)#cfs') \<in>  cptn_mod_nest_call"
  using a0 a1 a2
by (meson elim_cptn_mod_nest_call_n cptn_mod_nest_n_1) 

lemma cptn_mod_nest_tl_not_min:
  assumes a0:"(n,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" and
          a1:"cfg=(p,s)#cfg'" and
          a2:"\<not> (min_call n \<Gamma> cfg)"
  shows "\<not> (min_call n \<Gamma> cfg')"
proof (cases cfg')
  case Nil 
  have "(\<Gamma>, []) \<notin> cptn"
    using cptn.simps by auto
  then show ?thesis unfolding min_call_def
    using cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod local.Nil by blast  
next
  case (Cons xa cfga)
  then obtain q t where "xa = (q,t)" by fastforce
  then have "(n-1,\<Gamma>,cfg') \<in>  cptn_mod_nest_call"
    using a0 a1 a2 cptn_mod_nest_tl_n_1 Cons by fastforce
  also then have "(n,\<Gamma>,cfg') \<in>  cptn_mod_nest_call"
    using cptn_mod_nest_mono Nat.diff_le_self by blast
  ultimately show ?thesis unfolding min_call_def
    using a0 a2 min_call_def by force 
qed
  
  

definition cpn :: "nat \<Rightarrow> ('s,'p,'f,'e) body \<Rightarrow> ('s,'p,'f,'e) com \<Rightarrow> 
                  ('s,'f) xstate \<Rightarrow> (('s,'p,'f,'e) confs) set" 
where
 "cpn n \<Gamma> P s \<equiv> {(\<Gamma>1,l). l!0=(P,s) \<and> (n,\<Gamma>,l) \<in> cptn_mod_nest_call \<and> \<Gamma>1=\<Gamma>}"


lemma cptn_mod_same_n:
  assumes a0:"(\<Gamma>,cfs)\<in> cptn_mod" 
  shows "\<exists>n. (n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call"
proof -
 show ?thesis using cptn_mod_nest_mono cptn_mod_cptn_mod_nest
 by (metis a0 cptn_mod_nest_mono2 leI)
qed

lemma cptn_mod_same_n1:
  assumes a0:"(\<Gamma>,cfs)\<in> cptn_mod" and 
          a1:"(\<Gamma>,cfs1)\<in> cptn_mod"
  shows "\<exists>n. (n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call \<and> (n,\<Gamma>,cfs1) \<in>  cptn_mod_nest_call"
proof -
 show ?thesis using cptn_mod_nest_mono cptn_mod_cptn_mod_nest
 by (metis a0 a1 cptn_mod_nest_mono2 leI)
qed


lemma dropcptn_is_cptn1 [rule_format,elim!]:
  "\<forall>j<length c. (n,\<Gamma>,c) \<in> cptn_mod_nest_call \<longrightarrow> (n,\<Gamma>, drop j c) \<in> cptn_mod_nest_call"
proof -
  {fix j
   assume "j<length c \<and> (n,\<Gamma>,c) \<in> cptn_mod_nest_call"
   then have "(n,\<Gamma>, drop j c) \<in> cptn_mod_nest_call" 
   proof(induction j arbitrary: c)
     case 0 then show ?case by auto
   next
     case (Suc j) 
     then obtain a b c' where "c=a#b#c'"
       by (metis Cons_nth_drop_Suc Suc_lessE drop_0 less_trans_Suc zero_less_Suc)
     then also have "j<length (b#c')" using Suc by auto
     ultimately moreover have "(n, \<Gamma>, drop j (b # c')) \<in> cptn_mod_nest_call" using elim_cptn_mod_nest_call_n[of n \<Gamma> c] Suc
       by (metis surj_pair) 
     ultimately show ?case by auto  
   qed
 } thus ?thesis by auto 
qed

   

subsection \<open>Compositionality of the Semantics\<close>

subsubsection \<open>Definition of the conjoin operator\<close>

definition same_length :: "('s,'p,'f,'e) par_confs \<Rightarrow> (('s,'p,'f,'e) confs) list \<Rightarrow> bool" where
  "same_length c clist \<equiv> (\<forall>i<length clist. length(snd (clist!i))=length (snd c))"

lemma same_length_non_pair:
  assumes a1:"same_length c clist " and
          a2:"clist'=map (\<lambda>x. snd x) clist"
  shows "(\<forall>i <length clist'. length( (clist'!i))=length (snd c))"
using a1 a2 by (auto simp add: same_length_def)


definition same_state :: "('s,'p,'f,'e) par_confs \<Rightarrow> (('s,'p,'f,'e) confs) list \<Rightarrow> bool" where
  "same_state c clist \<equiv> (\<forall>i <length clist. \<forall>j<length (snd c). snd((snd c)!j) = snd((snd (clist!i))!j))"

lemma same_state_non_pair:
  assumes a1:"same_state c clist " and
          a2:"clist'=map (\<lambda>x. snd x) clist"
  shows "(\<forall>i <length clist'. \<forall>j<length (snd c). snd((snd c)!j) = snd( (clist'!i)!j))"
using a1 a2 by (auto simp add: same_state_def)

definition same_program :: "('s,'p,'f,'e) par_confs \<Rightarrow> (('s,'p,'f,'e) confs) list \<Rightarrow> bool" where
  "same_program c clist \<equiv> (\<forall>j<length (snd c). fst((snd c)!j) = map (\<lambda>x. fst(nth (snd x) j)) clist)"

lemma same_program_non_pair:
  assumes a1:"same_program c clist " and
          a2:"clist'=map (\<lambda>x. snd x) clist"
  shows "(\<forall>j<length (snd c). fst((snd c)!j) = map (\<lambda>x. fst(nth x j)) clist')"
using a1 a2 by (auto simp add: same_program_def)

definition same_functions :: "('s,'p,'f,'e) par_confs \<Rightarrow> (('s,'p,'f,'e) confs) list \<Rightarrow> bool" where
 "same_functions c clist \<equiv> \<forall>i <length clist. fst (clist!i) = fst c"

definition compat_label :: "('s,'p,'f,'e) par_confs \<Rightarrow> (('s,'p,'f,'e) confs) list \<Rightarrow> bool" where
  "compat_label c clist \<equiv> 
     (\<forall>j. Suc j<length (snd c) \<longrightarrow> 
         ( ((fst c)\<turnstile>\<^sub>p((snd c)!j)  \<rightarrow> ((snd c)!(Suc j))) \<and> 
            (\<exists>i<length clist. 
               ((fst (clist!i))\<turnstile>\<^sub>c ((snd (clist!i))!j)  \<rightarrow> ((snd (clist!i))!(Suc j))) \<and> 
            (\<forall>l<length clist. 
               l\<noteq>i \<longrightarrow>  (fst (clist!l))\<turnstile>\<^sub>c (snd (clist!l))!j  \<rightarrow>\<^sub>e ((snd (clist!l))!(Suc j))  ))) \<or> 
         ((fst c)\<turnstile>\<^sub>p((snd c)!j)  \<rightarrow>\<^sub>e ((snd c)!(Suc j)) \<and> 
          (\<forall>i<length clist.  (fst (clist!i))\<turnstile>\<^sub>c (snd (clist!i))!j  \<rightarrow>\<^sub>e ((snd (clist!i))!(Suc j))   )))"

lemma compat_label_tran_0:
 assumes assm1:"compat_label c clist \<and> length (snd c) > Suc 0" 
 shows  "((fst c)\<turnstile>\<^sub>p((snd c)!0)  \<rightarrow> ((snd c)!(Suc 0))) \<or> 
      ((fst c)\<turnstile>\<^sub>p((snd c)!0)  \<rightarrow>\<^sub>e ((snd c)!(Suc 0)))"    
  using assm1 unfolding compat_label_def
 by blast
  
  
definition conjoin :: "(('s,'p,'f,'e) par_confs) \<Rightarrow> (('s,'p,'f,'e) confs) list \<Rightarrow> bool"  ("_ \<propto> _" [65,65] 64) where
  "c \<propto> clist \<equiv> (same_length c clist) \<and> (same_state c clist) \<and> (same_program c clist) \<and> 
                (compat_label c clist) \<and> (same_functions c clist)"


lemma conjoin_same_length: 
   "c \<propto> clist \<Longrightarrow> \<forall>i < length (snd c). length (fst ((snd c)!i)) =  length clist"
proof (auto)
  fix i
  assume a1:"c \<propto> clist"
  assume a2:"i < length (snd c)"
  then have "(\<forall>j<length (snd c). fst((snd c)!j) = map (\<lambda>x. fst(nth (snd x) j)) clist)"
    using a1 unfolding conjoin_def same_program_def by auto
  thus "length (fst (snd c ! i)) = length clist" by (simp add: a2)
qed

lemma "c \<propto> clist \<Longrightarrow>
       i< length (snd c) \<and> j < length (snd c) \<Longrightarrow>  
       length (fst ((snd c)!i)) = length (fst ((snd c)!j))"
using conjoin_same_length by fastforce

lemma conjoin_same_length_i_suci:"c \<propto> clist \<Longrightarrow>
       Suc i< length (snd c) \<Longrightarrow>
       length (fst ((snd c)!i)) = length (fst ((snd c)!(Suc i)))"
using conjoin_same_length by fastforce

lemma conjoin_same_program_i:
  "c \<propto> clist \<Longrightarrow>
   j < length (snd c) \<Longrightarrow>
   i < length clist \<Longrightarrow>
   fst ((snd (clist!i))!j) = (fst ((snd c)!j))!i"
proof -
  assume a0:"c \<propto> clist" and
         a1:"j < length (snd c)" and
         a2:"i < length clist"
  have "length (fst ((snd c)!j)) = length clist"
    using conjoin_same_length a0 a1 by fastforce
  also have "fst (snd c ! j) = map (\<lambda>x. fst (snd x ! j)) clist"
    using a0 a1 unfolding conjoin_def same_program_def by fastforce
  ultimately show ?thesis using a2 by fastforce
qed

lemma conjoin_same_program_i_j:
  "c \<propto> clist \<Longrightarrow>
   Suc j < length (snd c) \<Longrightarrow>
   \<forall>l< length clist. fst ((snd (clist!l))!j) = fst ((snd (clist!l))!(Suc j)) \<Longrightarrow>
   fst ((snd c)!j) = (fst ((snd c)!(Suc j)))"
proof -
  assume a0:"c \<propto> clist" and
         a1:"Suc j < length (snd c)" and
         a2:"\<forall>l< length clist. fst ((snd (clist!l))!j) = fst ((snd (clist!l))!(Suc j))"
  have "length (fst ((snd c)!j)) = length clist"
    using conjoin_same_length a0 a1 by fastforce
  then have "map (\<lambda>x. fst (snd x ! j)) clist = map (\<lambda>x. fst (snd x ! (Suc j))) clist"
    using a2 by (metis (no_types, lifting) in_set_conv_nth map_eq_conv) 
  moreover have "fst (snd c ! j) = map (\<lambda>x. fst (snd x ! j)) clist"
    using a0 a1 unfolding conjoin_def same_program_def by fastforce
  moreover have "fst (snd c ! Suc j) = map (\<lambda>x. fst (snd x ! Suc j)) clist"
    using a0 a1 unfolding conjoin_def same_program_def by fastforce
  ultimately show ?thesis by fastforce
qed

lemma conjoin_last_same_state:
  assumes a0: "(\<Gamma>,l)\<propto> clist" and
   a1: "i < length clist" and
   a2: "(snd (clist!i))\<noteq>[]"
   shows "snd (last (snd (clist!i))) = snd (last l)"
proof -
  have "length l = length (snd (clist!i))" 
    using a0 a1 unfolding conjoin_def same_length_def by fastforce
  also then have length_l:"length l \<noteq>0" using a2 by fastforce
  ultimately have "last (snd (clist!i)) = (snd (clist!i))!((length l)-1)" 
    using a1 a2 
    by (simp add: last_conv_nth)
  thus ?thesis using length_l a0 a1 unfolding conjoin_def same_state_def
    by (simp add:  a2 last_conv_nth )      
qed

lemma list_eq_if [rule_format]: 
  "\<forall>ys. xs=ys \<longrightarrow> (length xs = length ys) \<longrightarrow> (\<forall>i<length xs. xs!i=ys!i)"
  by (induct xs) auto



lemma list_eq: "(length xs = length ys \<and> (\<forall>i<length xs. xs!i=ys!i)) = (xs=ys)"
apply(rule iffI)
 apply clarify
 apply(erule nth_equalityI)
 apply simp+
done

lemma nth_tl: "\<lbrakk> ys!0=a; ys\<noteq>[] \<rbrakk> \<Longrightarrow> ys=(a#(tl ys))"
  by (cases ys) simp_all

lemma nth_tl_if [rule_format]: "ys\<noteq>[] \<longrightarrow> ys!0=a \<longrightarrow> P ys \<longrightarrow> P (a#(tl ys))"
  by (induct ys) simp_all

lemma nth_tl_onlyif [rule_format]: "ys\<noteq>[] \<longrightarrow> ys!0=a \<longrightarrow> P (a#(tl ys)) \<longrightarrow> P ys"
  by (induct ys) simp_all

lemma nth_tl_eq [rule_format]: "ys\<noteq>[] \<longrightarrow> ys!0=a \<longrightarrow> P (a#(tl ys)) = P ys"
  by (induct ys) simp_all

lemma nth_tl_pair: "\<lbrakk>p=(u,ys); ys!0=a; ys\<noteq>[] \<rbrakk> \<Longrightarrow> p=(u,(a#(tl ys)))"
by (simp add: SmallStepCon.nth_tl)

lemma nth_tl_eq_Pair [rule_format]: "p=(u,ys) \<longrightarrow> ys\<noteq>[] \<longrightarrow> ys!0=a \<longrightarrow> P ((u,a#(tl ys))) = P (u,ys)"
  by (induct ys) simp_all



lemma tl_in_cptn: "\<lbrakk> (g,a#xs) \<in>cptn; xs\<noteq>[] \<rbrakk> \<Longrightarrow> (g,xs)\<in>cptn"
  by (force elim: cptn.cases)


lemma tl_zero[rule_format]: 
  " Suc j<length ys \<longrightarrow> P (ys!Suc j) \<longrightarrow> P (tl(ys)!j)"
  by (simp add: List.nth_tl)

lemma tl_zero1[rule_format]:
  "Suc j<length ys \<longrightarrow>P (tl(ys)!j) \<longrightarrow>P (ys!Suc j)"
 by (simp add: List.nth_tl)

lemma tl_zero_eq [rule_format]:
  "Suc j<length ys \<longrightarrow> (P (tl(ys)!j) = P (ys!Suc j))"
by (simp add: List.nth_tl)

lemma tl_zero_eq' :
   "\<forall>j. Suc j<length ys \<longrightarrow> (P (tl(ys)!j) = P (ys!Suc j))"
using tl_zero_eq by blast

lemma tl_zero_pair:"i < length ys \<Longrightarrow> length ys = length zs \<Longrightarrow>
       Suc j < length (snd (ys!i)) \<Longrightarrow>
       snd (zs!i) = tl (snd (ys!i)) \<Longrightarrow>        
       P ((snd (ys!i))!(Suc j)) =
       P ((snd (zs!i))!j)"  
  by (simp add: tl_zero_eq)


lemma tl_zero_pair':"\<forall>i < length ys. length ys = length zs \<longrightarrow>
       Suc j < length (snd (ys!i)) \<longrightarrow>
       snd (zs!i) = tl (snd (ys!i)) \<longrightarrow>        
       (P ((snd (ys!i))!(Suc j)) =
       P ((snd (zs!i))!j))"  
using tl_zero_pair by blast

lemma tl_zero_pair2:"i < length ys \<Longrightarrow> length ys = length zs \<Longrightarrow>
       Suc (Suc j) < length (snd (ys!i)) \<Longrightarrow>
       snd (zs!i) = tl (snd (ys!i)) \<Longrightarrow>        
       P ((snd (ys!i))!(Suc (Suc j))) ((snd (ys!i))!(Suc j))  =
       P ((snd (zs!i))!(Suc j)) ((snd (zs!i))!j)"  
  by (simp add: tl_zero_eq)

lemma tl_zero_pair2':"\<forall>i < length ys. length ys = length zs \<longrightarrow>
       Suc (Suc j) < length (snd (ys!i)) \<longrightarrow>
       snd (zs!i) = tl (snd (ys!i)) \<longrightarrow>        
       P ((snd (ys!i))!(Suc (Suc j))) ((snd (ys!i))!(Suc j))  =
       P ((snd (zs!i))!(Suc j)) ((snd (zs!i))!j)"  
using tl_zero_pair2  by blast

lemma tl_zero_pair21:"\<forall>i < length ys. length ys = length zs \<longrightarrow>
       Suc (Suc j) < length (snd (ys!i)) \<longrightarrow>
       snd (zs!i) = tl (snd (ys!i)) \<longrightarrow>        
       P  ((snd (ys!i))!(Suc j))  ((snd (ys!i))!(Suc (Suc j)))=
       P ((snd (zs!i))!j) ((snd (zs!i))!(Suc j)) "
by (metis SmallStepCon.nth_tl list.size(3) not_less0 nth_Cons_Suc)  

lemma tl_pair:"Suc (Suc j) < length l \<Longrightarrow>     
       l1 = tl l \<Longrightarrow>
       P (l!(Suc (Suc j))) (l!(Suc j)) =
       P (l1!(Suc j)) (l1!j)"
by (simp add: tl_zero_eq)

lemma list_as_map: 
  assumes 
     a1:"length clist > 0" and 
     a2: "xs = (map (\<lambda>x. fst (hd x)) clist)" and
     a3: "ys = (map (\<lambda>x. tl x) clist)" and
     a4: "\<forall>i< length clist. length (clist!i) > 0" and     
     a5: "\<forall>i < length clist. \<forall>j< length clist. \<forall>k<length  (clist!i).
           snd ((clist!i)!k) = snd ((clist!j)!k)" and
     a6: "\<forall>i < length clist. \<forall>j< length clist. 
            length (clist!i) = length (clist!j)" 
     shows "clist = map (\<lambda>i. (fst i,snd ((clist!0)!0))#snd i) (zip xs ys)"
proof-
  let ?clist'= "map (\<lambda>i. (fst i,snd ((clist!0)!0))#snd i) (zip xs ys)"
  have lens:"length clist = length ?clist'"  using a2 a3 by auto   
  have "(\<forall>i<length clist. clist ! i = ?clist' ! i)" 
  proof -
    {
      fix i    
      assume a11:"i<length clist"
      have xs_clist:"xs!i = fst (hd (clist!i))" using a2 a11 by auto
      have ys_clist:"ys!i = tl (clist ! i)" using a3 a11 by auto
      have snd_zero:"snd (hd (clist!i)) = snd ((clist!0)!0)" using a5 a4 
        by (metis (no_types, lifting) a1 a11 hd_conv_nth less_numeral_extra(3) list.size(3))
      then have "(\<lambda>i. (fst i,snd ((clist!0)!0))#snd i) ((zip xs ys)!i) = clist !i"               
        proof -
          have f1: "length xs = length clist"
            using a2 length_map by blast
          have "\<not> (0::nat) < 0"
            by (meson less_not_refl)
          thus ?thesis
            using f1 by (metis (lifting) a11 a3 a4 
                         fst_conv length_map list.exhaust_sel 
                         list.size(3) nth_zip prod.collapse 
                         snd_conv snd_zero xs_clist ys_clist)
        qed      
      then have "clist ! i = ?clist' ! i" using lens a11 by force
    } 
    thus ?thesis by auto    
  qed
  thus ?thesis using lens list_eq by blast
qed

lemma list_as_map': 
  assumes 
     a1:"length clist > 0" and 
     a2: "xs = (map (\<lambda>x. hd x) clist)" and
     a3: "ys = (map (\<lambda>x. tl x) clist)" and
     a4: "\<forall>i< length clist. length (clist!i) > 0"
     shows "clist = map (\<lambda>i. (fst i)#snd i) (zip xs ys)"
proof-
  let ?clist'= "map (\<lambda>i.(fst i)#snd i) (zip xs ys)"
  have lens:"length clist = length ?clist'" using a2 a3 by auto  
  have "(\<forall>i<length clist. clist ! i = ?clist' ! i)" 
  proof -
    {
      fix i    
      assume a11:"i<length clist"
      have xs_clist:"xs!i = hd (clist!i)" using a2 a11 by auto
      have ys_clist:"ys!i = tl (clist ! i)" using a3 a11 by auto 
      then have "(\<lambda>i. fst i#snd i) ((zip xs ys)!i) = clist !i"  
        using xs_clist ys_clist a11 a2 a3 a4 by fastforce  
      then have "clist ! i = ?clist' ! i" using lens a11 by force
    } 
    thus ?thesis by auto    
  qed
  thus ?thesis using lens list_eq by blast
qed


lemma conjoin_tl: 
  assumes 
    a1: "(\<Gamma>,x#xs) \<propto> ys" and
    a2:"zs = map (\<lambda>i. (fst i, tl (snd i))) ys"    
   shows "(\<Gamma>,xs) \<propto> zs"
proof -
  have s_p:"same_program (\<Gamma>,x#xs) ys" using a1 unfolding conjoin_def by simp
  have s_l:"same_length (\<Gamma>,x#xs) ys" using a1 unfolding conjoin_def by simp
  have "\<forall>i<length zs. snd (zs!i) = tl (snd (ys!i))"
    by (simp add: a2)    
  {
    have "same_length (\<Gamma>,xs) zs" using a1 a2 unfolding conjoin_def 
     by (simp add: same_length_def)
  } moreover note same_len = this
  {    
    {
       fix j
       assume a11:"j<length (snd (\<Gamma>, xs))"                                                               
       then have fst_suc:"fst (snd (\<Gamma>, xs) ! j) = fst(snd (\<Gamma>,x#xs)! Suc j)"
         by auto       
       then have "fst (snd (\<Gamma>, xs) ! j) = map (\<lambda>x. fst (snd x ! j)) zs" 
       proof -
         have s_l_y_z:"length ys = length zs" using a2 by fastforce
         have Suc_j_l_ys:"\<forall>i < length ys. Suc j < length (snd (ys!i))" 
           using a11 s_l unfolding same_length_def by fastforce
         have tail: "\<forall>i < length ys. snd (zs!i) = tl (snd (ys!i))" using a2 
           by fastforce                  
         then have l_xs_zs_eq:"length (fst (snd (\<Gamma>, xs) ! j)) = length zs"
            using fst_suc s_l_y_z s_p a11 unfolding same_program_def by auto         
         then have "\<forall>i<length ys. 
           fst (snd (\<Gamma>, x#xs) ! Suc j)!i = fst (snd (ys!i) ! (Suc j))"
             using s_p a11 unfolding same_program_def by fastforce
         then have "\<forall>i<length zs. 
           fst (snd (\<Gamma>, x#xs) ! Suc j)!i = fst (snd (zs!i) ! (j))"
           using Suc_j_l_ys tail s_l_y_z tl_zero_pair by metis
        then have "\<forall>i<length zs. 
           fst (snd (\<Gamma>, xs) ! j)!i = map (\<lambda>x. fst (snd x !  j)) zs!i"
          using fst_suc by auto
        also have "length (fst (snd (\<Gamma>, xs) ! j)) = 
                   length (map (\<lambda>x. fst (snd x !  j)) zs) " 
          using l_xs_zs_eq by auto
        ultimately show ?thesis using  l_xs_zs_eq list_eq by metis
       qed                 
    }
    then have "same_program  (\<Gamma>,xs) zs"
    unfolding conjoin_def  same_program_def same_length_def     
    by blast    
  }moreover note same_prog = this
  {
    have "same_state  (\<Gamma>,xs) zs" 
    using a1 a2 unfolding conjoin_def same_length_def same_state_def
    apply auto
    by (metis (no_types, hide_lams) List.nth_tl Suc_less_eq diff_Suc_1 length_tl nth_Cons_Suc)    
  }moreover note same_sta = this
  {
    have "same_functions  (\<Gamma>,xs) zs" 
     using a1 a2 unfolding conjoin_def
     apply auto
     apply (simp add: same_functions_def)          
     done
  }moreover note same_fun = this
  { {
      fix j
      assume a11:"Suc j<length (snd (\<Gamma>, xs))"
      have s_l_y_z:"length ys = length zs" using a2 by fastforce
      have Suc_j_l_ys:"\<forall>i < length ys. Suc (Suc j) < length (snd (ys!i))" 
        using a11 s_l unfolding same_length_def by fastforce
      have tail: "\<forall>i < length ys. snd (zs!i) = tl (snd (ys!i))" using a2 
        by fastforce    
      have same_env: "\<forall>i < length ys. (fst (ys!i)) = \<Gamma>"
        using a1 unfolding conjoin_def same_functions_def by auto
      have fst: "\<forall>x. fst(\<Gamma>, x) = \<Gamma>" by auto
      then have fun_ys_eq_fun_zs: "\<forall>i < length ys. (fst (ys!i)) = (fst (zs!i))"
        using same_env s_l_y_z
        proof -
          have "\<forall>n. \<not> n < length ys \<or> fst (zs ! n) = fst (ys ! n)"
            by (simp add: a2)
          thus ?thesis
            by presburger
        qed
      have suc_j:"Suc (Suc j) < length (snd (\<Gamma>, x#xs))" using a11 by auto      
     then have or_compat:"( (\<Gamma> \<turnstile>\<^sub>p((snd  (\<Gamma>, x#xs))!(Suc j))  \<rightarrow> ((snd  (\<Gamma>, x#xs))!(Suc (Suc j)))) \<and> 
            (\<exists>i<length ys. 
               ((fst (ys!i))\<turnstile>\<^sub>c ((snd (ys!i))!(Suc j))  \<rightarrow> ((snd (ys!i))!(Suc (Suc j)))) \<and> 
            (\<forall>l<length ys. 
               l\<noteq>i \<longrightarrow> (fst (ys!l))\<turnstile>\<^sub>c (snd (ys!l))!(Suc j)  \<rightarrow>\<^sub>e ((snd (ys!l))!(Suc (Suc j)))  ))) \<or> 
            (\<Gamma>\<turnstile>\<^sub>p((snd  (\<Gamma>, x#xs))!(Suc j))  \<rightarrow>\<^sub>e ((snd  (\<Gamma>, x#xs))!(Suc (Suc j))) \<and> 
            (\<forall>i<length ys. (fst (ys!i))\<turnstile>\<^sub>c (snd (ys!i))!(Suc j)  \<rightarrow>\<^sub>e ((snd (ys!i))!(Suc (Suc j)))))"
        using suc_j a1 same_env unfolding conjoin_def compat_label_def fst by auto
       then have 
         "( (fst (\<Gamma>, xs) \<turnstile>\<^sub>p((snd  (\<Gamma>, xs))!(j))  \<rightarrow> ((snd  (\<Gamma>,xs))!((Suc j)))) \<and> 
              (\<exists>i<length zs. 
                 ((fst (zs!i))\<turnstile>\<^sub>c ((snd (zs!i))!( j))  \<rightarrow> ((snd (zs!i))!( (Suc j)))) \<and> 
              (\<forall>l<length zs. 
                 l\<noteq>i \<longrightarrow> (fst (zs!l))\<turnstile>\<^sub>c (snd (zs!l))!( j)  \<rightarrow>\<^sub>e (( snd (zs!l))!( (Suc j)))  )))\<or>
               ((fst (\<Gamma>, xs)\<turnstile>\<^sub>p((snd  (\<Gamma>, xs))!(j))  \<rightarrow>\<^sub>e ((snd  (\<Gamma>, xs))!((Suc j))) \<and> 
           (\<forall>i<length zs. (fst (zs!i))\<turnstile>\<^sub>c (snd (zs!i))!(j)  \<rightarrow>\<^sub>e ((snd (zs!i))!((Suc j)))   )))"
       proof 
         assume a21:"( (\<Gamma> \<turnstile>\<^sub>p((snd  (\<Gamma>, x#xs))!(Suc j))  \<rightarrow> ((snd  (\<Gamma>, x#xs))!(Suc (Suc j)))) \<and> 
              (\<exists>i<length ys. 
                 ((fst (ys!i))\<turnstile>\<^sub>c ((snd (ys!i))!(Suc j))  \<rightarrow> ((snd (ys!i))!(Suc (Suc j)))) \<and> 
              (\<forall>l<length ys. 
                 l\<noteq>i \<longrightarrow> (fst (ys!l))\<turnstile>\<^sub>c (snd (ys!l))!(Suc j)  \<rightarrow>\<^sub>e ((snd (ys!l))!(Suc (Suc j)))  )))" 
          then obtain i where 
              f1:"( (\<Gamma> \<turnstile>\<^sub>p((snd  (\<Gamma>, x#xs))!(Suc j))  \<rightarrow> ((snd  (\<Gamma>, x#xs))!(Suc (Suc j)))) \<and> 
              (i<length ys \<and> 
                 ((fst (ys!i))\<turnstile>\<^sub>c ((snd (ys!i))!(Suc j))  \<rightarrow> ((snd (ys!i))!(Suc (Suc j)))) \<and> 
              (\<forall>l<length ys. 
                 l\<noteq>i \<longrightarrow> (fst (ys!l))\<turnstile>\<^sub>c (snd (ys!l))!(Suc j)  \<rightarrow>\<^sub>e ((snd (ys!l))!(Suc (Suc j)))  )))"       
           by auto 
          then have "( (\<Gamma> \<turnstile>\<^sub>p((snd  (\<Gamma>, x#xs))!(Suc j))  \<rightarrow> ((snd  (\<Gamma>, x#xs))!(Suc (Suc j)))) \<and> 
              (\<exists>i<length ys. 
                 ((fst (ys!i))\<turnstile>\<^sub>c ((snd (zs!i))!( j))  \<rightarrow> ((snd (zs!i))!( (Suc j)))) \<and> 
              (\<forall>l<length ys. 
                 l\<noteq>i \<longrightarrow> (fst (ys!l))\<turnstile>\<^sub>c (snd (zs!l))!( j)  \<rightarrow>\<^sub>e (( snd (zs!l))!( (Suc j)))  )))"
            proof -
                have f1: "\<Gamma>\<turnstile>\<^sub>p snd (\<Gamma>, x # xs) ! Suc j \<rightarrow> snd (\<Gamma>, x # xs) ! Suc (Suc j) \<and> i < length ys \<and> fst (ys ! i)\<turnstile>\<^sub>c snd (ys ! i) ! Suc j \<rightarrow> snd (ys ! i) ! Suc (Suc j) \<and> (\<forall>n. (\<not> n < length ys \<or> n = i) \<or> fst (ys ! n)\<turnstile>\<^sub>c snd (ys ! n) ! Suc j \<rightarrow>\<^sub>e snd (ys ! n) ! Suc (Suc j))"
                  using f1 by blast
                have f2: "j < length (snd (\<Gamma>, xs))"
                  by (meson Suc_lessD a11)
                have f3: "\<forall>n. \<not> n < length zs \<or> length (snd (zs ! n)) = length (snd (\<Gamma>, xs))"
                  using same_len same_length_def by blast
                have "\<forall>n. \<not> n < length ys \<or> snd (zs ! n) = tl (snd (ys ! n))"
                  using tail by blast
                thus ?thesis
                  using f3 f2 f1 by (metis (no_types) List.nth_tl a11 s_l_y_z)
              qed           
             then have"( (\<Gamma> \<turnstile>\<^sub>p((snd  (\<Gamma>, xs))!(j))  \<rightarrow> ((snd  (\<Gamma>,xs))!((Suc j)))) \<and> 
              (\<exists>i<length zs. 
                 ((fst (zs!i))\<turnstile>\<^sub>c ((snd (zs!i))!( j))  \<rightarrow> ((snd (zs!i))!( (Suc j)))) \<and> 
              (\<forall>l<length zs. 
                 l\<noteq>i \<longrightarrow> (fst (zs!l))\<turnstile>\<^sub>c (snd (zs!l))!( j)  \<rightarrow>\<^sub>e (( snd (zs!l))!( (Suc j)))  )))"
              using same_env s_l_y_z fun_ys_eq_fun_zs by force
             then have"( (fst (\<Gamma>, xs) \<turnstile>\<^sub>p((snd  (\<Gamma>, xs))!(j))  \<rightarrow> ((snd  (\<Gamma>,xs))!((Suc j)))) \<and> 
              (\<exists>i<length zs. 
                 ((fst (zs!i))\<turnstile>\<^sub>c ((snd (zs!i))!( j))  \<rightarrow> ((snd (zs!i))!( (Suc j)))) \<and> 
              (\<forall>l<length zs. 
                 l\<noteq>i \<longrightarrow> (fst (zs!l))\<turnstile>\<^sub>c (snd (zs!l))!( j)  \<rightarrow>\<^sub>e (( snd (zs!l))!( (Suc j)))  )))"
             by auto
             thus ?thesis
             by auto
      next    
        assume a22:
            "(\<Gamma>\<turnstile>\<^sub>p((snd  (\<Gamma>, x#xs))!(Suc j))  \<rightarrow>\<^sub>e ((snd  (\<Gamma>, x#xs))!(Suc (Suc j))) \<and> 
            (\<forall>i<length ys. (fst (ys!i))\<turnstile>\<^sub>c (snd (ys!i))!(Suc j)  \<rightarrow>\<^sub>e ((snd (ys!i))!(Suc (Suc j)))   ))"
        then have 
          "(\<Gamma>\<turnstile>\<^sub>p((snd  (\<Gamma>, x#xs))!(Suc j))  \<rightarrow>\<^sub>e ((snd  (\<Gamma>, x#xs))!(Suc (Suc j))) \<and> 
           (\<forall>i<length ys. (fst (ys!i))\<turnstile>\<^sub>c (snd (zs!i))!(j)  \<rightarrow>\<^sub>e ((snd (zs!i))!((Suc j)))   ))"
        using Suc_j_l_ys tail s_l_y_z tl_zero_pair21 by metis
        then have
          "(\<Gamma>\<turnstile>\<^sub>p((snd  (\<Gamma>, xs))!(j))  \<rightarrow>\<^sub>e ((snd  (\<Gamma>, xs))!((Suc j))) \<and> 
           (\<forall>i<length zs. (fst (zs!i))\<turnstile>\<^sub>c (snd (zs!i))!(j)  \<rightarrow>\<^sub>e ((snd (zs!i))!((Suc j)))   ))"
          using same_env s_l_y_z fun_ys_eq_fun_zs by fastforce
        thus ?thesis by auto 
      qed
    }
    then have "compat_label  (\<Gamma>,xs) zs"
    using compat_label_def by blast 
  } note same_label = this
  ultimately show ?thesis using conjoin_def by auto
qed



lemma clist_tail: 
  assumes 
    a1:"length xs = length clist" and
    a2: "ys = (map (\<lambda>i. (\<Gamma>,(fst i,s)#snd i)) (zip xs clist))"
 shows "\<forall>i < length ys. tl (snd (ys!i)) = clist!i "
using a1 a2
proof -   
   show ?thesis using a2
   by (simp add: a1)           
qed   


lemma clist_map: 
   assumes 
    a1:"length xs = length clist" 
   shows "clist = map ((\<lambda>p. tl (snd p)) \<circ> (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))) (zip xs clist)"
proof -
  have f1: "map snd (zip xs clist) = clist"
    using a1 map_snd_zip by blast
  have "map snd (zip xs clist) = map ((\<lambda>p. tl (snd p)) \<circ> (\<lambda>p. (\<Gamma>, (fst p, s) # snd p))) (zip xs clist)"
    by simp
  thus ?thesis
    using f1 by presburger
qed


lemma clist_map1: 
   assumes 
    a1:"length xs = length clist"     
   shows "clist = map (\<lambda>p. tl (snd p)) (map (\<lambda>i. (\<Gamma>,(fst i,s)#snd i)) (zip xs clist))"
proof -
   have "clist = map ((\<lambda>p. tl (snd p)) \<circ> (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))) (zip xs clist)" 
   using a1  clist_map by fastforce
   thus ?thesis by auto
qed

lemma clist_map2:
     "(clist = map (\<lambda>p. tl (snd p)) (l::('a \<times>'b list) list) ) \<Longrightarrow>
       clist = map (\<lambda>p. (snd p)) (map (\<lambda>p. (fst p, tl (snd p))) (l::('a \<times>'b list) list)) "
by auto

lemma map_snd:
   assumes a1: "y = map  (\<lambda>x. f x) l"
   shows   "y=(map snd (map (\<lambda>x. (g x, f x)) l)) "
by (simp add: assms)
 
lemmas map_snd_sym = map_snd[THEN sym]

lemma map_snd':
   shows   " map  (\<lambda>x. f x) l=(map snd (map (\<lambda>x. (g x, f x)) l)) "
by simp

lemma clist_snd:
 assumes a1: "(\<Gamma>, a # ys) \<propto> map (\<lambda>x. (fst x, tl (snd x)))
                    (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i)) (zip xs clist))" and
         a2: "length clist > 0 \<and> length clist = length xs"
 shows "clist = (map snd
          (map (\<lambda>x. (\<Gamma>, (fst x, snd (clist ! 0 ! 0)) # snd x))
            (zip (map (\<lambda>x. fst (hd x)) clist) (map tl clist))))"
proof -
     let ?concat_zip = "(\<lambda>i. (\<Gamma>, (fst i, s) # snd i))"  
     let ?clist_ext = "map ?concat_zip (zip xs clist)"
     let ?exec_run = "(xs, s) # a # ys"
     let ?exec = "(\<Gamma>,?exec_run)"
     let ?exec_ext = "map (\<lambda>x. (fst x, tl (snd x))) ?clist_ext"
     let ?zip = "(zip (map (\<lambda>x. fst (hd x)) clist) 
                         (map (\<lambda>x. tl x) clist))"
  have \<Gamma>_all: "\<forall>i < length ?clist_ext. fst (?clist_ext !i) = \<Gamma>"
       by auto       
  have len:"length xs = length clist" using a2 by auto
  then have len_clist_exec:
   "length clist = length ?exec_ext" 
   by fastforce    
  then have len_clist_exec_map:
    "length ?exec_ext = 
              length (map (\<lambda>x. (\<Gamma>, (fst x,snd ((clist!0)!0))#snd x)) 
                          ?zip)" 
   by fastforce               
  then have clist_snd:"clist = map (\<lambda>x. snd x) ?exec_ext"
    using clist_map1 [of xs clist \<Gamma> s] clist_map2 len by blast   
  then have clist_len_eq_ays: 
      "\<forall>i < length clist. length( (clist!i))=length (snd (\<Gamma>,a#ys))"      
    using len  same_length_non_pair a1 conjoin_def
    by blast
  then have clist_gz:"\<forall>i < length clist. length (clist!i) > 0" 
    by fastforce
  have clist_len_eq: 
     "\<forall>i < length clist. \<forall>j < length clist. 
        length (clist ! i) = length (clist ! j)" 
    using clist_len_eq_ays by auto          
  have clist_same_state: 
    "\<forall>i < length clist. \<forall>j< length clist. \<forall>k<length  (clist!i).
       snd ((clist!i)!k) = snd ((clist!j)!k)"
  proof -
    have 
      "(\<forall>i <length clist. \<forall>j<length (snd (\<Gamma>, a # ys)). snd((snd (\<Gamma>, a # ys))!j) = snd( (clist!i)!j))"
      using len clist_snd conjoin_def a1 conjoin_def same_state_non_pair 
    by blast
    thus ?thesis using clist_len_eq_ays by (metis (no_types))
  qed      
  then have clist_map:
    "clist = map (\<lambda>i. (fst i,snd ((clist!0)!0))#snd i) ?zip"
    using list_as_map a2 clist_gz clist_len_eq by blast      
  moreover have "map (\<lambda>i. (fst i,snd ((clist!0)!0))#snd i) ?zip =
             map snd (map (\<lambda>x. (\<Gamma>, (fst x, snd (clist ! 0 ! 0)) # snd x))
       (zip (map (\<lambda>x. fst (hd x)) clist) (map tl clist)))"
  using map_snd' by auto
  ultimately show ?thesis by auto   
qed

lemma list_as_zip:
 assumes a1: "(\<Gamma>, a # ys) \<propto> map (\<lambda>x. (fst x, tl (snd x)))
                    (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i)) (zip xs clist))" and
         a2: "length clist > 0 \<and> length clist = length xs"
 shows "  map (\<lambda>x. (fst x, tl (snd x)))
                    (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i)) (zip xs clist)) =
          map (\<lambda>x. (\<Gamma>, (fst x,snd ((clist!0)!0))#snd x)) 
                       (zip (map (\<lambda>x. fst (hd x)) clist) 
                         (map (\<lambda>x. tl x) clist))"
proof -
     let ?concat_zip = "(\<lambda>i. (\<Gamma>, (fst i, s) # snd i))"  
     let ?clist_ext = "map ?concat_zip (zip xs clist)"
     let ?exec_run = "(xs, s) # a # ys"
     let ?exec = "(\<Gamma>,?exec_run)"
     let ?exec_ext = "map (\<lambda>x. (fst x, tl (snd x))) ?clist_ext"
     let ?zip = "(zip (map (\<lambda>x. fst (hd x)) clist) 
                         (map (\<lambda>x. tl x) clist))"
  have \<Gamma>_all: "\<forall>i < length ?clist_ext. fst (?clist_ext !i) = \<Gamma>"
       by auto       
  have len:"length xs = length clist" using a2 by auto
  then have len_clist_exec:
   "length clist = length ?exec_ext" 
   by fastforce    
  then have len_clist_exec_map:
    "length ?exec_ext = 
              length (map (\<lambda>x. (\<Gamma>, (fst x,snd ((clist!0)!0))#snd x)) 
                          ?zip)" 
   by fastforce               
  then have clist_snd:"clist = map (\<lambda>x. snd x) ?exec_ext"
    using clist_map1 [of xs clist \<Gamma> s] clist_map2 len by blast   
  then have clist_len_eq_ays: 
      "\<forall>i < length clist. length( (clist!i))=length (snd (\<Gamma>,a#ys))"      
    using len  same_length_non_pair a1 conjoin_def
    by blast
  then have clist_gz:"\<forall>i < length clist. length (clist!i) > 0" 
    by fastforce
  have clist_len_eq: 
     "\<forall>i < length clist. \<forall>j < length clist. 
        length (clist ! i) = length (clist ! j)" 
    using clist_len_eq_ays by auto          
  have clist_same_state: 
    "\<forall>i < length clist. \<forall>j< length clist. \<forall>k<length  (clist!i).
       snd ((clist!i)!k) = snd ((clist!j)!k)"
  proof -
    have 
      "(\<forall>i <length clist. \<forall>j<length (snd (\<Gamma>, a # ys)). snd((snd (\<Gamma>, a # ys))!j) = snd( (clist!i)!j))"
      using len clist_snd conjoin_def a1 conjoin_def same_state_non_pair 
    by blast
    thus ?thesis using clist_len_eq_ays by (metis (no_types))
  qed      
  then have clist_map:
    "clist = map (\<lambda>i. (fst i,snd ((clist!0)!0))#snd i) ?zip"
    using list_as_map a2 clist_gz clist_len_eq by blast      
  then have "\<forall>i < length clist. 
                clist ! i = (fst (?zip!i),snd ((clist!0)!0)) # snd (?zip!i)"
  using len nth_map length_map by (metis (no_types, lifting))
  then have 
    "\<forall>i < length clist. 
     ?exec_ext ! i = (\<Gamma>, (fst (?zip!i),snd ((clist!0)!0)) # snd (?zip!i))" 
  using \<Gamma>_all len  by fastforce           
  moreover have "\<forall>i < length clist. 
    (\<Gamma>, (fst (?zip!i),snd ((clist!0)!0)) # snd (?zip!i)) = 
    (map (\<lambda>x. (\<Gamma>, (fst x,snd ((clist!0)!0))#snd x)) 
                          ?zip)!i" 
  by auto        
  ultimately have 
     "\<forall>i < length clist. 
       ?exec_ext ! i =(map (\<lambda>x. (\<Gamma>, (fst x,snd ((clist!0)!0))#snd x)) 
                          ?zip)!i" 
  by auto
  then also have "length clist = length ?exec_ext" 
  using len by fastforce 
  ultimately have exec_ext_eq_clist_map:
     "\<forall>i < length ?exec_ext. 
       ?exec_ext ! i =(map (\<lambda>x. (\<Gamma>, (fst x,snd ((clist!0)!0))#snd x)) 
                          ?zip)!i" 
  by presburger
  then moreover have "length ?exec_ext = 
              length (map (\<lambda>x. (\<Gamma>, (fst x,snd ((clist!0)!0))#snd x)) 
                          ?zip)" 
  using len clist_map by fastforce    
  ultimately show ?thesis
     using list_eq by blast  
qed

lemma hd_nth:
   assumes a1:"i< length l \<and> ( length( (l!i)) > 0)"
   shows "f (hd (l!i)) = f (nth (l!i) 0)"
using assms hd_conv_nth by fastforce

lemma map_hd_nth:
   assumes a1:"(\<forall>i <length l. length( (l!i)) > 0)"
   shows "map (\<lambda>x. f (hd x)) l = map (\<lambda>x. f (nth (x) 0)) l"
proof -  
   have "\<forall>i < length l. (map (\<lambda>x. f (hd x)) l)!i = f (nth (l!i) 0)"
    using hd_nth a1 by auto
  moreover have "\<forall>i < length l. (map (\<lambda>x. f (nth x 0)) l)!i = f (nth (l!i) 0)"
    using hd_nth a1 by auto
  ultimately have f1:"\<forall>i < length l. (map (\<lambda>x. f (hd x)) l)!i =(map (\<lambda>x. f (nth x 0)) l)!i "
    by auto
  moreover have f2:"length (map (\<lambda>x. f (hd x)) l) = length l"
    by auto   
  moreover have "length (map (\<lambda>x. f (nth x 0)) l) = length l" by auto
  ultimately show ?thesis using nth_equalityI by metis
qed

lemma "i<length clist \<Longrightarrow> clist!i = (x1,ys) \<Longrightarrow> ys = (map (\<lambda>x. (fst (hd (snd x)),s)#tl (snd x)) clist)!i \<Longrightarrow>
         ys = (map (\<lambda>x. (fst x, s)#snd x) 
               (zip (map (\<lambda>x. fst (hd (snd x))) clist) 
                    (map (\<lambda>x. tl (snd x)) clist)))!i"
proof (induct ys)
  case Nil thus ?case by auto
next
  case (Cons y ys) 
  have "\<forall>n ps f. \<not> n < length ps \<or> map f ps ! n = (f (ps ! n::'a \<times> ('b \<times> 'c) list)::('b \<times> 'c) list)"
    by force
  hence "y # ys = (fst (hd (snd (clist ! i))), s) # tl (snd (clist ! i))"
    using Cons.prems(1) Cons.prems(3) by presburger
  thus ?case
    using Cons.prems(1) by auto
qed

  

lemma clist_map_zip:"xs\<noteq>[] \<Longrightarrow> (\<Gamma>,(xs,s)#ys) \<propto> clist \<Longrightarrow> 
      clist = map (\<lambda>i. (\<Gamma>,(fst i,s)#(snd i))) (zip xs ((map (\<lambda>x. tl (snd x))) clist))"
proof -
  let ?clist = "map snd clist"
  assume a1: "xs\<noteq>[]"
  assume a2:  "(\<Gamma>,(xs,s)#ys) \<propto> clist"
  then have all_in_clist_not_empty:"\<forall>i < length ?clist. (?clist!i) \<noteq> []"
   unfolding conjoin_def same_length_def by auto
  then have hd_clist:"\<forall>i < length ?clist. hd (?clist!i) = (?clist!i)!0" 
     by (simp add: hd_conv_nth)  
  then have all_xs:"\<forall>i< length ?clist. fst (hd (?clist!i)) = xs!i"
   using  a2 unfolding conjoin_def same_program_def by auto
  
  then have  all_s: "\<forall>i < length ?clist. snd (hd (?clist!i)) = s"
    using a2 hd_clist unfolding conjoin_def same_state_def by fastforce
  have fst_clist_\<Gamma>:"\<forall>i < length clist. fst (clist!i) = \<Gamma>"
    using a2 unfolding conjoin_def same_functions_def by auto 
   have p2:"length xs = length clist" using conjoin_same_length a2
   by fastforce
  
  
  then have "\<forall>i< length (map (\<lambda>x. fst (hd x)) ?clist). 
               (map (\<lambda>x. fst (hd x)) ?clist)!i = xs!i"
    using all_xs by auto
  also have "length (map (\<lambda>x. fst (hd x)) ?clist) = length xs" using p2 by auto
  ultimately have "(map (\<lambda>x. fst (hd x)) ?clist) = xs"
   using nth_equalityI by metis
  then have xs_clist:"map (\<lambda>x. fst (hd (snd x))) clist = xs" by auto
       
  have clist_hd_tl:"\<forall>i < length ?clist. ?clist!i = hd (?clist!i) # (tl (?clist!i))"
   using all_in_clist_not_empty list.exhaust_sel by blast   
  then have "\<forall>i < length ?clist. ?clist!i =(fst  (hd (?clist!i)),snd  (hd (?clist!i)))# (tl (?clist!i))"
    by auto
  then have "?clist = map (\<lambda>x. (fst (hd x),snd (hd x))#tl x) ?clist" 
   using length_map list_eq_iff_nth_eq list_update_id map_update nth_list_update_eq
   by (metis (no_types, lifting) length_map list_eq_iff_nth_eq list_update_id map_update nth_list_update_eq)
  then have "?clist = map (\<lambda>x. (fst (hd x),s)#tl x) ?clist"
   using all_s length_map nth_equalityI nth_map
    by (metis (no_types, lifting) ) 
  then have map_clist:"map (\<lambda>x. (fst (hd (snd x)),s)#tl (snd x)) clist = ?clist" 
   by auto   
  then have "(map (\<lambda>x. (fst x, s)#snd x) 
               (zip (map (\<lambda>x. fst (hd (snd x))) clist) 
                    (map (\<lambda>x. tl (snd x)) clist))) =  ?clist"     
    using map_clist  by (auto intro: nth_equalityI) 
  then have "\<forall>i<length clist. clist!i =  (\<Gamma>,(map (\<lambda>x. (fst x, s)#snd x) 
               (zip xs 
                   (map (\<lambda>x. tl (snd x)) clist)))!i)" 
   using  xs_clist fst_clist_\<Gamma>  by auto   
  also have "length clist = length (map (\<lambda>i. (\<Gamma>,(fst i,s)#(snd i))) (zip xs ((map (\<lambda>x. tl (snd x))) clist)))" 
    using p2 by auto
  ultimately show "clist = map (\<lambda>i. (\<Gamma>,(fst i,s)#(snd i))) (zip xs ((map (\<lambda>x. tl (snd x))) clist))" 
    using length_map length_zip nth_equalityI nth_map 
    by (metis (no_types, lifting)) 
qed
            
lemma aux_if' : 
  assumes a:"length clist > 0 \<and> length clist = length xs \<and> 
             (\<forall>i<length xs. (\<Gamma>,(xs!i,s)#clist!i) \<in> cptn) \<and> 
             ((\<Gamma>,(xs, s)#ys) \<propto> map (\<lambda>i. (\<Gamma>,(fst i,s)#snd i)) (zip xs clist))"
  shows "(\<Gamma>,(xs, s)#ys) \<in> par_cptn"
using a
proof (induct ys arbitrary: xs s clist) 
  case Nil then show ?case by (simp add: par_cptn.ParCptnOne)
next
  case (Cons a ys xs s clist)     
     let ?concat_zip = "(\<lambda>i. (\<Gamma>, (fst i, s) # snd i))"  
     let ?com_clist_xs = "map ?concat_zip (zip xs clist)"
     let ?xs_a_ys_run = "(xs, s) # a # ys"
     let ?xs_a_ys_run_exec = "(\<Gamma>,?xs_a_ys_run)"
     let ?com_clist' = "map (\<lambda>x. (fst x, tl (snd x))) ?com_clist_xs"
     let ?xs' = "(map (\<lambda>x. fst (hd x)) clist)"     
     let ?clist' = "(map (\<lambda>x. tl x) clist)"
     let ?zip_xs'_clist' = "zip ?xs' 
                            ?clist'"         
     obtain as sa where a_pair:"a=(as,sa)" by fastforce
       let ?comp_clist'_alt = "map (\<lambda>x. (\<Gamma>, (fst x,snd ((clist!0)!0))#snd x)) ?zip_xs'_clist' "
       let ?clist'_alt = "map (\<lambda>x. snd x) ?comp_clist'_alt"
       let ?comp_a_ys = "(\<Gamma>, (as,sa) # ys)"   
     have conjoin_hyp1:
       "(\<Gamma>, (as,sa) # ys) \<propto> ?com_clist'"
       using conjoin_tl using a_pair Cons by blast     
     then have conjoin_hyp:
       "(\<Gamma>, (as,sa) # ys) \<propto> map (\<lambda>x. (\<Gamma>, (fst x,snd ((clist!0)!0))#snd x)) ?zip_xs'_clist'"
     using list_as_zip Cons.prems by fastforce    
     have len:"length xs = length clist" using Cons by auto 
     have clist_snd_map:
        "(map snd
          (map (\<lambda>x. (\<Gamma>, (fst x, snd (clist ! 0 ! 0)) # snd x))
         (zip (map (\<lambda>x. fst (hd x)) clist) (map tl clist)))) = clist"
       using clist_snd Cons.prems conjoin_hyp1 by fastforce
     have eq_len_clist_clist':
       "length ?clist' > 0" using Cons.prems by auto  
     have "(\<forall>i <length clist. \<forall>j<length (snd ?comp_a_ys). snd((snd ?comp_a_ys)!j) = snd( (clist!i)!j))"
        using clist_snd_map conjoin_hyp conjoin_def same_state_non_pair[of ?comp_a_ys ?comp_clist'_alt ?clist'_alt]
         by fastforce   
     then have "\<forall>i<length clist.
                  sa = snd ( (clist ! i)!0)" by fastforce
     also have clist_i_grz:"(\<forall>i <length clist. length( (clist!i)) > 0)"
         using clist_snd_map conjoin_hyp conjoin_def same_length_non_pair[of ?comp_a_ys ?comp_clist'_alt ?clist'_alt]
     by fastforce  
     ultimately have all_i_sa_hd_clist:"\<forall>i<length clist.
                  sa = snd (hd (clist ! i))"
     by (simp add: hd_conv_nth)      
     have as_sa_eq_xs'_s':"as = ?xs' \<and>  sa = snd ((clist!0)!0)" 
     proof -              
       have "(\<forall>j<length (snd ?comp_a_ys). fst((snd ?comp_a_ys)!j) = 
                map (\<lambda>x. fst(nth x j)) ?clist'_alt)"       
       using conjoin_hyp conjoin_def same_program_non_pair[of ?comp_a_ys ?comp_clist'_alt ?clist'_alt]
       by fast
       then have are_eq:"fst((snd ?comp_a_ys)!0) = 
                map (\<lambda>x. fst(nth x 0)) ?clist'_alt" by fastforce
       have fst_exec_is_as:"fst((snd ?comp_a_ys)!0) =as" by auto              
       then have "map (\<lambda>x. fst(hd x)) clist=map (\<lambda>x. fst(x!0)) clist"
         using map_hd_nth clist_i_grz by auto 
       then have "map (\<lambda>x. fst(nth x 0)) ?clist'_alt =?xs'" using clist_snd_map map_hd_nth
        by fastforce
       moreover have "(\<forall>i <length clist. \<forall>j<length (snd ?comp_a_ys). snd((snd ?comp_a_ys)!j) = snd( (clist!i)!j))"
        using clist_snd_map conjoin_hyp conjoin_def same_state_non_pair[of ?comp_a_ys ?comp_clist'_alt ?clist'_alt]
         by fastforce
       ultimately show ?thesis using are_eq fst_exec_is_as
          using Cons.prems by force 
    qed
    then have conjoin_hyp:
       "(\<Gamma>, (as,sa) # ys) \<propto> map (\<lambda>x. (\<Gamma>, (fst x,sa)#snd x))
                            (zip as (map tl clist))"
    using conjoin_hyp by auto
    then have eq_len_as_clist':
       "length as = length ?clist'" using Cons.prems as_sa_eq_xs'_s' by auto
    then have len_as_ys_eq:"length as = length xs" using Cons.prems by auto
    have " (\<forall>i<length as. (\<Gamma>, ((as!i),sa)#(map (\<lambda>x. tl x) clist)!i) \<in> cptn)" 
     using Cons.prems cptn_dest clist_snd_map len 
    proof -     
      have "\<forall>i<length clist. clist!i = (hd (clist!i))#(tl (clist!i))" 
       using clist_i_grz 
      by auto
      then have "(\<forall>i<length clist. (\<Gamma>, (xs ! i, s) # (hd (clist!i))#(tl (clist!i))) \<in> cptn)"
      using Cons.prems by auto
      then have f1:"(\<forall>i<length clist. (\<Gamma>, (hd (clist!i))#(tl (clist!i))) \<in> cptn)"
      by (metis list.distinct(2) tl_in_cptn) 
      then have "(\<forall>i<length clist. (\<Gamma>, ((as!i),sa)#(tl (clist!i))) \<in> cptn)"
      using as_sa_eq_xs'_s' all_i_sa_hd_clist by auto      
      then have "(\<forall>i<length clist. (\<Gamma>, ((as!i),sa)#(map (\<lambda>x. tl x) clist)!i) \<in> cptn)"
      by auto
      thus ?thesis using  len clist_i_grz len_as_ys_eq by auto
   qed
   then have a_ys_par_cptn:"(\<Gamma>, (as, sa) # ys) \<in> par_cptn"           
   using 
    conjoin_hyp eq_len_clist_clist' eq_len_as_clist'[THEN sym] Cons.hyps
   by blast  
   have \<Gamma>_all: "\<forall>i < length ?com_clist_xs. fst (?com_clist_xs !i) = \<Gamma>"
   by auto
   have Gamma: "\<Gamma>= (fst ?xs_a_ys_run_exec)" by fastforce  
   have exec: "?xs_a_ys_run = (snd ?xs_a_ys_run_exec)" by fastforce  
   have split_par:
       "\<Gamma>\<turnstile>\<^sub>p ((xs, s) # a # ys) ! 0 \<rightarrow> ((a # ys) ! 0) \<or>
        \<Gamma>\<turnstile>\<^sub>p ((xs, s) # a # ys) ! 0 \<rightarrow>\<^sub>e ((a # ys) ! 0)"     
       using compat_label_def compat_label_tran_0
             Cons.prems Gamma exec 
             compat_label_tran_0[of "(\<Gamma>, (xs, s) # a # ys)" 
                                   "(map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i)) (zip xs clist))"]    
       unfolding conjoin_def by auto      
     {
      assume "\<Gamma>\<turnstile>\<^sub>p ((xs, s) # a # ys) ! 0 \<rightarrow> ((a # ys) ! 0)"      
      then have  " (\<Gamma>, (xs, s) # a # ys) \<in> par_cptn" 
      using a_ys_par_cptn a_pair par_cptn.ParCptnComp by fastforce
     } note env_sol=this
     {
      assume " \<Gamma>\<turnstile>\<^sub>p ((xs, s) # a # ys) ! 0 \<rightarrow>\<^sub>e ((a # ys) ! 0)"      
      then have env_tran:" \<Gamma>\<turnstile>\<^sub>p (xs, s)  \<rightarrow>\<^sub>e (as,sa)" using a_pair by auto
      have "xs = as"
       by (meson env_pe_c_c'_false env_tran)
      then have " (\<Gamma>, (xs, s) # a # ys) \<in> par_cptn" 
      using a_ys_par_cptn a_pair env_tran ParCptnEnv  by blast
     }
     then show "(\<Gamma>, (xs, s) # a # ys) \<in> par_cptn" using env_sol Cons split_par by fastforce
qed

lemma mapzip_upd:" length as = length clist  \<Longrightarrow>
       (map (\<lambda>j. (as ! j, sa) # clist ! j) [0..<length as]) =  
       map (\<lambda>j. ((fst j, sa)#snd j)) (zip as clist)"
proof -    
    assume a2: "length as = length clist"   
    have "\<forall>i < length  (map (\<lambda>j. (as ! j, sa) # clist ! j) [0..<length as]). (map (\<lambda>j. (as ! j, sa) # clist ! j) [0..<length as])!i = map (\<lambda>j. ((fst j, sa)#snd j)) (zip as clist)!i"  
     using a2
      by auto
  moreover have "length (map (\<lambda>j. (as ! j, sa) # clist ! j) [0..<length as]) =
         length (map (\<lambda>j. ((fst j, sa)#snd j)) (zip as clist))"
     using a2 by auto   
  ultimately have "(map (\<lambda>j. (as ! j, sa) # clist ! j) [0..<length as]) = map (\<lambda>j. ((fst j, sa)#snd j)) (zip as clist)"
     using nth_equalityI by blast
  thus "map (\<lambda>j. (as ! j, sa) # clist ! j) [0..<length as] = 
        map (\<lambda>j. (fst j, sa) # snd j) (zip as clist) "
      by auto
qed

lemma aux_if : 
  assumes a:" length clist = length xs \<and> 
             (\<forall>i<length xs. (\<Gamma>,(xs!i,s)#clist!i) \<in> cptn) \<and> 
             ((\<Gamma>,(xs, s)#ys) \<propto> map (\<lambda>i. (\<Gamma>,(fst i,s)#snd i)) (zip xs clist))"
  shows "(\<Gamma>,(xs, s)#ys) \<in> par_cptn"
using a
proof (cases "length clist")
 case 0 
    then have clist_empty:"clist = []" by auto
    then have map_clist_empty:"map (\<lambda>i. (\<Gamma>,(fst i,s)#snd i)) (zip xs clist) = []"
      by fastforce
    then have conjoin:"(\<Gamma>,(xs, s)#ys) \<propto> []" using a by auto   
    then have all_eq:"\<forall>j<length (snd (\<Gamma>,(xs, s)#ys)). fst (snd (\<Gamma>,(xs, s)#ys) ! j) = []"
      using conjoin_def same_program_def
    by (simp add: conjoin_def same_program_def)
    from conjoin          
    show ?thesis using conjoin
    proof (induct ys arbitrary: s xs) 
       case Nil then show ?case by (simp add: par_cptn.ParCptnOne)
    next
       case (Cons a ys)          
         then have conjoin_ind:"(\<Gamma>, (xs, s) # a # ys) \<propto> []" by auto
         then have  "(\<Gamma>,(a # ys)) \<propto> []" 
           by (auto simp add:conjoin_def same_length_def 
                 same_state_def same_program_def same_functions_def
                 compat_label_def)
         moreover obtain as sa where pair_a: "a=(as,sa)" using Cons by fastforce
         ultimately have ays_par_cptn:"(\<Gamma>, a # ys) \<in> par_cptn" using Cons.hyps by auto
         have "\<forall>j. Suc j<length (snd (\<Gamma>,(xs, s)#(as,sa)#ys)) \<longrightarrow> 
                   \<not>(\<exists>i<length []. 
                     ((fst ([]!i))\<turnstile>\<^sub>c ((snd ([]!i))!j)  \<rightarrow> ((snd ([]!i))!(Suc j))))"
         using conjoin_def compat_label_def by fastforce
         then have "(\<forall>j. Suc j<length (snd (\<Gamma>,(xs, s)#(as,sa)#ys)) \<longrightarrow> 
                    ((fst (\<Gamma>,(xs, s)#(as,sa)#ys))\<turnstile>\<^sub>p((snd (\<Gamma>,(xs, s)#(as,sa)#ys))!j)  \<rightarrow>\<^sub>e ((snd (\<Gamma>,(xs, s)#(as,sa)#ys))!(Suc j))))"
         using conjoin_def compat_label_def conjoin_ind pair_a by blast
         then have env_tran:"\<Gamma>\<turnstile>\<^sub>p (xs, s)  \<rightarrow>\<^sub>e (as,sa)" by auto               
         then show " (\<Gamma>, (xs, s) # a # ys) \<in> par_cptn" 
         using ays_par_cptn pair_a env_tran ParCptnEnv env_pe_c_c'_false by blast
   qed
next
 case Suc
    then have "length clist > 0" by auto
    then show ?thesis using a aux_if' by blast
qed

lemma snormal_enviroment:"s = Normal nsa \<or> s = sa \<and> (\<forall>sa. s \<noteq> Normal sa) \<Longrightarrow>
        \<Gamma>\<turnstile>\<^sub>c (x, s) \<rightarrow>\<^sub>e (x, sa)"
by (metis Env Env_n)

lemma aux_onlyif [rule_format]: "\<forall>xs s. (\<Gamma>,(xs, s)#ys) \<in> par_cptn \<longrightarrow> 
  (\<exists>clist. (length clist = length xs) \<and> 
  (\<Gamma>, (xs, s)#ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i,s)#(snd i))) (zip xs clist) \<and> 
  (\<forall>i<length xs. (\<Gamma>, (xs!i,s)#(clist!i)) \<in> cptn))"
proof (induct ys) 
  case Nil 
  {fix xs s
    assume "(\<Gamma>, [(xs, s)]) \<in> par_cptn"
    have f1:"length (map (\<lambda>i. []) [0..<length xs]) = length xs" by auto
    have f2:"(\<Gamma>, [(xs, s)]) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                              (zip xs (map (\<lambda>i. []) [0..<length xs]))"
    unfolding conjoin_def same_length_def same_functions_def same_state_def same_program_def compat_label_def            
      by(simp, rule nth_equalityI,simp,simp)
    note h = conjI[OF f1 f2]
    have f3:"(\<forall>i<length xs. (\<Gamma>, (xs ! i, s) # (map (\<lambda>i. []) [0..<length xs]) ! i) \<in> cptn)"
      by (simp add: cptn.CptnOne)
    note this = conjI[OF h f3]
    }
     thus ?case by blast
next
  case (Cons a ys) 
  {fix  xs s
   assume a1:"(\<Gamma>, (xs, s) # a # ys) \<in> par_cptn"
   then obtain as sa where a_pair: "a=(as,sa)" by fastforce
   then have par_cptn':"(\<Gamma>,( (as,sa)#ys)) \<in> par_cptn"
    using a1 par_cptn_dest by blast 
   then obtain clist where hyp: "
              length clist = length as \<and>
              (\<Gamma>, (as, sa) #
                   ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, sa) # snd i)) (zip as clist) \<and>
              (\<forall>i<length as. (\<Gamma>, (as ! i, sa) # clist ! i) \<in> cptn)"
     using Cons.hyps by fastforce
   have a11:"(\<Gamma>, (xs, s) # (as,sa) # ys) \<in> par_cptn" using a1 a_pair by auto
   have par_cptn_dest:"\<Gamma>\<turnstile>\<^sub>p (xs, s) \<rightarrow>\<^sub>e (as, sa) \<or> \<Gamma>\<turnstile>\<^sub>p (xs, s) \<rightarrow> (as, sa)"
     using par_cptn_elim_cases par_cptn' a1  a_pair by blast 
   {
     assume a1: "\<Gamma>\<turnstile>\<^sub>p (xs, s) \<rightarrow>\<^sub>e (as, sa)"          
     then have xs_as_eq:"xs=as" by (meson env_pe_c_c'_false)
     then have ce:"\<forall>i < length xs. \<Gamma>\<turnstile>\<^sub>c (xs!i, s) \<rightarrow>\<^sub>e (as!i, sa)" using a1 pe_ce by fastforce
     let ?clist="(map (\<lambda>j. (xs!j, sa)#(clist!j)) [0..<length xs])"    
     have s1:"length ?clist = length xs"
       by auto
     have s2:"(\<forall>i<length xs. (\<Gamma>, (xs ! i, s) # ?clist ! i) \<in> cptn)"  
        using a1 hyp CptnEnv xs_as_eq ce by fastforce
     have s3:"(\<Gamma>, (xs, s) #
                       (as,sa) # ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist)"     
     proof -        
         have s_len:"same_length (\<Gamma>, (xs, s) # (as,sa) # ys) 
                           (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist))"
               using hyp conjoin_def same_length_def xs_as_eq a1 by fastforce
         have s_state: "same_state (\<Gamma>, (xs, s) # (as,sa) # ys) 
                           (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist))"
              using hyp
              apply (simp add:hyp conjoin_def same_state_def  a1)              
              apply clarify
              apply(case_tac j) 
              by (simp add: xs_as_eq,simp add: xs_as_eq)
         have s_function: "same_functions (\<Gamma>, (xs, s) # (as,sa) # ys) 
                           (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist))"
              using hyp conjoin_def same_functions_def a1 by fastforce
         have s_program: "same_program (\<Gamma>, (xs, s) # (as,sa) # ys) 
                           (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist))"          
              using hyp
              apply (simp add:hyp conjoin_def same_program_def same_length_def a1)
              apply clarify
              apply(case_tac j)                
                apply(rule nth_equalityI) 
                apply(simp,simp)              
              by(rule nth_equalityI, simp add: hyp xs_as_eq, simp add:xs_as_eq)
         have s_compat:"compat_label (\<Gamma>, (xs, s) # (xs,sa) # ys) 
                           (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist))" 
            using hyp a1 pe_ce
            apply (simp add:hyp conjoin_def compat_label_def)
            apply clarify
            apply(case_tac j,simp add: xs_as_eq)
               apply blast
              apply (simp add: xs_as_eq step_e.intros step_pe.intros)
             apply clarify
            apply(erule_tac x=nat in allE,erule impE,assumption)             
            apply(erule disjE,simp)
            apply clarify
            apply(rule_tac x=i in exI) 
            using hyp by (fastforce)+                            
        thus ?thesis using s_len s_program s_state s_function conjoin_def xs_as_eq
            by blast
     qed
     then have 
      "(\<exists>clist.
                  length clist = length xs \<and>
                  (\<Gamma>, (xs, s) #
                       a # ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs clist) \<and>
                  (\<forall>i<length xs. (\<Gamma>, (xs ! i, s) # clist ! i) \<in> cptn))"
     using s1 s2 a_pair by blast
   } note s1=this

   {
     assume a1':"\<Gamma>\<turnstile>\<^sub>p (xs, s) \<rightarrow> (as, sa)"
     then obtain i r where 
       inter_tran:"i < length xs \<and> \<Gamma>\<turnstile>\<^sub>c (xs ! i, s) \<rightarrow> (r, sa) \<and> as = xs[i := r]" 
     using step_p_pair_elim_cases by metis     
     then have xs_as_eq_len: "length xs = length as" by simp
     from inter_tran 
      have s_states:"\<exists>nsa. s=Normal nsa \<or> (s=sa \<and> (\<forall>sa. (s\<noteq>Normal sa)))"
      using step_not_normal_s_eq_t by blast
     have as_xs:"\<forall>i'<length as. (i'=i \<and> as!i'=r) \<or> (as!i'=xs!i')" 
       using xs_as_eq_len by (simp add: inter_tran nth_list_update)
     let ?clist="(map (\<lambda>j. (as!j, sa)#(clist!j)) [0..<length xs]) [i:=((r, sa)#(clist!i))]"
     have s1:"length ?clist = length xs"
       by auto
     have s2:"(\<forall>i'<length xs. (\<Gamma>, (xs ! i', s) # ?clist ! i') \<in> cptn)" 
        proof -
         {fix i'
          assume a1:"i' < length xs"          
          have "(\<Gamma>, (xs ! i', s) # ?clist ! i') \<in> cptn"
          proof (cases "i=i'")
            case True 
             thus ?thesis using inter_tran  hyp cptn.CptnComp               
              apply simp 
              by fastforce  
          next              
            case False            
            thus ?thesis using s_states inter_tran  False hyp cptn.CptnComp a1
              apply clarify
              apply simp
              apply(erule_tac x=i' in allE)
              apply (simp)
              apply(rule CptnEnv) 
              by (auto simp add: Env Env_n)
          qed
         } 
        thus ?thesis by fastforce
      qed
     then have s3:"(\<Gamma>, (xs, s) #
                       (as,sa) # ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist)"
     proof -        
        from hyp have 
         len_list:"length clist = length as" by auto
        from hyp have same_len:"same_length (\<Gamma>, (as, sa) # ys)  
                      (map (\<lambda>i. (\<Gamma>, (fst i, sa) # snd i)) (zip as clist))"
          using conjoin_def by auto        
        have s_len: "same_length (\<Gamma>, (xs, s) # (as,sa) # ys) 
                           (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist))"  
          using 
            same_len  inter_tran  
            unfolding conjoin_def same_length_def
            apply clarify 
            apply(case_tac "i=ia")            
            by (auto simp add: len_list)            
        have s_state: "same_state (\<Gamma>, (xs, s) # (as,sa) # ys) 
                           (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist))"
              using hyp inter_tran unfolding conjoin_def same_state_def
               apply clarify
               apply(case_tac j, simp, simp (no_asm_simp))
               apply(case_tac "i=ia",simp , simp )
              by (metis (no_types, hide_lams) as_xs nth_list_update_eq xs_as_eq_len)              
        have s_function: "same_functions (\<Gamma>, (xs, s) # (as,sa) # ys) 
                           (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist))"
              using hyp conjoin_def same_functions_def a1 by fastforce
        have s_program: "same_program (\<Gamma>, (xs, s) # (as,sa) # ys) 
                           (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist))"          
          using hyp inter_tran unfolding conjoin_def same_program_def
           apply clarify
           apply(case_tac j,simp)           
           apply(rule nth_equalityI,simp,simp)
           apply simp
           apply(rule nth_equalityI,simp,simp)
           apply(erule_tac x=nat and P="\<lambda>j. H j \<longrightarrow> (fst (a j))=((b j))" for H a b in allE)
           apply(case_tac nat)
           apply clarify
           apply(case_tac "i=ia",simp,simp)
           apply clarify
           by(case_tac "i=ia",simp,simp)                   
        have s_compat:"compat_label (\<Gamma>, (xs, s) # (as,sa) # ys) 
                           (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist))" 
        using inter_tran hyp s_states
        unfolding conjoin_def compat_label_def
         apply clarify
         apply(case_tac j)
          apply(rule conjI,simp)
           apply(erule ParComp,assumption)
           apply clarify
           apply(rule exI[where x=i],simp)
          apply clarify
          apply (rule snormal_enviroment,assumption)
         apply simp
         apply(erule_tac x=nat and P="\<lambda>j. H j \<longrightarrow> (P j \<or> Q j)" for H P Q in allE,simp)
         apply (thin_tac "s = Normal nsa \<or> s = sa \<and> (\<forall>sa. s \<noteq> Normal sa)")
        apply(erule disjE )
         apply clarify
         apply(rule_tac x=ia in exI,simp)
         apply(rule conjI)
          apply(case_tac "i=ia",simp,simp)
         apply clarify
         apply(case_tac "i=l",simp)
          apply(case_tac "l=ia",simp,simp)
          apply(erule_tac x=l in allE,erule impE,assumption,erule impE, assumption,simp)
         apply simp
         apply(erule_tac x=l in allE,erule impE,assumption,erule impE, assumption,simp)
        apply clarify
        apply (thin_tac " \<forall>ia<length xs. (\<Gamma>, (xs[i := r] ! ia, sa) # clist ! ia) \<in> cptn")
        apply(erule_tac x=ia and P="\<lambda>j. H j \<longrightarrow> (P j)" for H P in allE, erule impE, assumption)
        by(case_tac "i=ia",simp,simp)               
        thus ?thesis using s_len s_program s_state s_function conjoin_def  
          by blast
     qed     
     then have "(\<exists>clist.
                  length clist = length xs \<and>
                  (\<Gamma>, (xs, s) #
                       a # ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs clist) \<and>
                  (\<forall>i<length xs. (\<Gamma>, (xs ! i, s) # clist ! i) \<in> cptn))"
     using s1 s2 a_pair by blast
   } 
   then have 
      "(\<exists>clist.
                  length clist = length xs \<and>
                  (\<Gamma>, (xs, s) #
                       a # ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs clist) \<and>
                  (\<forall>i<length xs. (\<Gamma>, (xs ! i, s) # clist ! i) \<in> cptn))"
      using s1 par_cptn_dest by fastforce
  }  
  thus ?case by auto
qed  

lemma one_iff_aux_if:"xs\<noteq>[] \<Longrightarrow> (\<forall>ys. ((\<Gamma>,((xs, s)#ys)) \<in> par_cptn) = 
 (\<exists>clist. length clist= length xs \<and> 
 ((\<Gamma>,(xs, s)#ys) \<propto> map (\<lambda>i. (\<Gamma>,(fst i,s)#(snd i))) (zip xs clist)) \<and> 
 (\<forall>i<length xs. (\<Gamma>,(xs!i,s)#(clist!i)) \<in> cptn))) \<Longrightarrow>
 (par_cp \<Gamma> (xs) s = {(\<Gamma>1,c). \<exists>clist. (length clist)=(length xs) \<and>
 (\<forall>i<length clist. clist!i \<in> cp \<Gamma> (xs!i) s) \<and> (\<Gamma>,c) \<propto> clist \<and> \<Gamma>1=\<Gamma>})"
proof
  assume a1:"xs\<noteq>[]"
  assume a2:"\<forall>ys. ((\<Gamma>, (xs, s) # ys) \<in> par_cptn) =
         (\<exists>clist.
             length clist = length xs \<and>
             (\<Gamma>,
              (xs, s) #
              ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                      (zip xs clist) \<and>
             (\<forall>i<length xs.
                 (\<Gamma>, (xs ! i, s) # clist ! i) \<in> cptn))"         
   show "par_cp \<Gamma> xs s \<subseteq> 
             {(\<Gamma>1, c). \<exists>clist.
               length clist = length xs \<and>
               (\<forall>i<length clist. clist ! i \<in> cp \<Gamma> (xs ! i) s) \<and>
               (\<Gamma>, c) \<propto> clist \<and> \<Gamma>1 = \<Gamma>}"
   proof-{     
     fix x
     let ?show = "x\<in> {(\<Gamma>1, c). \<exists>clist.
       length clist = length xs \<and>
       (\<forall>i<length clist. clist ! i \<in> cp \<Gamma> (xs ! i) s) \<and>
        (\<Gamma>, c) \<propto> clist \<and> \<Gamma>1 = \<Gamma>}"
     assume a3:"x\<in>par_cp \<Gamma> xs s"   
     then obtain y where x_pair: "x=(\<Gamma>,y)"
       unfolding par_cp_def by auto       
     have ?show          
     proof (cases y)
        case Nil then 
         show ?show using a1 a2 a3 x_pair
          unfolding par_cp_def cp_def
          by (force elim:par_cptn.cases)
     next 
        case (Cons a list) then
          show ?show using a1 a2 a3 x_pair
          unfolding par_cp_def cp_def         
          by(auto, rule_tac x="map (\<lambda>i. (\<Gamma>,(fst i, s) # snd i)) (zip xs clist)" in exI,simp)
     qed
   } thus ?thesis using a1 a2 by auto 
   qed
   {   
   show "{(\<Gamma>1, c). \<exists>clist.
          length clist = length xs \<and>
          (\<forall>i<length clist. clist ! i \<in> cp \<Gamma> (xs ! i) s) \<and>
          (\<Gamma>, c) \<propto> clist \<and> \<Gamma>1 = \<Gamma>} \<subseteq> par_cp \<Gamma> xs s" using a1 a2 
   proof-
     { 
     fix x
     assume a3:"x\<in>{(\<Gamma>1, c). \<exists>clist.
          length clist = length xs \<and>
          (\<forall>i<length clist. clist ! i \<in> cp \<Gamma> (xs ! i) s) \<and>
          (\<Gamma>, c) \<propto> clist \<and> \<Gamma>1 = \<Gamma>}"
     then obtain c where x_pair: "x=(\<Gamma>,c)"  by auto
     then obtain clist where 
      props:"length clist = length xs \<and>
           (\<forall>i<length clist. clist ! i \<in> cp \<Gamma> (xs ! i) s) \<and>
           (\<Gamma>, c) \<propto> clist " using a3 by auto
     then have "x\<in>par_cp \<Gamma> xs s"
       proof (cases c)
         case Nil 
         have clist_0: 
           "clist ! 0 \<in> cp \<Gamma> (xs ! 0) s" using props a1 
         by auto
         thus "x\<in>par_cp \<Gamma> xs s"  
           using a1 a2 props Nil x_pair
         unfolding cp_def conjoin_def same_length_def 
         apply clarify                  
         by(erule cptn.cases,fastforce,fastforce,fastforce)
       next
         case (Cons a ys) 
         then obtain a1 a2 where a_pair: "a=(a1,a2)" 
           using props by fastforce 
         from a2 have 
               a2:"(((\<Gamma>, (xs, s) # ys) \<in> par_cptn) =
                   (\<exists>clist. length clist = length xs \<and>
                   (\<Gamma>, (xs, s) # ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i)) (zip xs clist) \<and>
                   (\<forall>i<length xs. (\<Gamma>, (xs ! i, s) # clist ! i) \<in> cptn)))" by auto
         have a2_s:"a2=s" using a1 props a_pair Cons
           unfolding  conjoin_def   same_state_def  cp_def         
           by force
         have a1_xs:"a1 = xs"
           using  props a_pair Cons 
           unfolding par_cp_def conjoin_def  same_program_def cp_def           
           apply clarify
           apply(erule_tac x=0 and P="\<lambda>j. H j \<longrightarrow> (fst (s j))=((t j))" for H s t in allE)                      
           by(rule nth_equalityI,auto)   
         then have conjoin_clist_xs:"(\<Gamma>, (xs,s)#ys) \<propto> clist"     
           using a1  props a_pair Cons a1_xs a2_s by auto
         also then have "clist = map (\<lambda>i. (\<Gamma>,(fst i,s)#(snd i))) (zip xs ((map (\<lambda>x. tl (snd x))) clist))"             
           using clist_map_zip a1  by fastforce
         ultimately have conjoin_map:"(\<Gamma>, (xs, s) # ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i)) (zip xs ((map (\<lambda>x. tl (snd x))) clist))"
           using props x_pair Cons a_pair a1_xs a2_s by auto    
         have "\<And>n. \<not> n < length xs \<or> clist ! n \<in> {(f, ps). ps ! 0 = (xs ! n, a2) \<and> (\<Gamma>, ps) \<in> cptn \<and> f = \<Gamma>}"
               using a1_xs a2_s props cp_def by fastforce
         then have clist_cptn:"(\<forall>i<length clist. (fst (clist!i) = \<Gamma>) \<and> 
                                 (\<Gamma>, snd (clist!i)) \<in> cptn \<and>
                                 (snd (clist!i))!0 = (xs!i,s))"
         using a1_xs a2_s props by fastforce         
                       
          {fix i
          assume a4: "i<length xs"     
          then have clist_i_cptn:"(fst (clist!i) = \<Gamma>) \<and> 
                     (\<Gamma>, snd (clist!i)) \<in> cptn \<and>
                     (snd (clist!i))!0 = (xs!i,s)"
           using props clist_cptn by fastforce 
          from a4 props have a4':"i<length clist" by auto
          have lengz:"length (snd (clist!i))>0" 
            using conjoin_clist_xs a4'
            unfolding  conjoin_def same_length_def 
           by auto
          then have clist_hd_tl:"snd (clist!i) =  hd (snd (clist!i)) # tl (snd (clist ! i))"
            by auto        
          also have " hd (snd (clist!i)) =  (snd (clist!i))!0"
            using a4' lengz by (simp add: hd_conv_nth)
          ultimately have clist_i_tl:"snd (clist!i) =  (xs!i,s) # tl (snd (clist ! i))"
            using clist_i_cptn by fastforce
          also have "tl (snd (clist ! i)) = map (\<lambda>x. tl (snd x)) clist!i"
            using nth_map a4' 
          by auto
          ultimately have snd_clist:"snd (clist!i) =  (xs ! i, s) # map (\<lambda>x. tl (snd x)) clist ! i"
            by auto
          also have "(clist!i) = (fst (clist!i),snd (clist!i))"
            by auto
          ultimately have "(clist!i) =(\<Gamma>, (xs ! i, s) # map (\<lambda>x. tl (snd x)) clist ! i)"
           using clist_i_cptn by auto
          then have "(\<Gamma>, (xs ! i, s) # map (\<lambda>x. tl (snd x)) clist ! i) \<in> cptn" 
             using clist_i_cptn by auto
          } 
          then have clist_in_cptn:"(\<forall>i<length xs. (\<Gamma>, (xs ! i, s) # ((map (\<lambda>x. tl (snd x))) clist) ! i) \<in> cptn)"
          by auto
         have same_length_clist_xs:"length ((map (\<lambda>x. tl (snd x))) clist)  = length xs"
           using props by auto
         then have "(\<exists>clist. length clist = length xs \<and>
                        (\<Gamma>, (xs, s) # ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i)) (zip xs clist) \<and>
                        (\<forall>i<length xs. (\<Gamma>, (xs ! i, s) # clist ! i) \<in> cptn))"
         using  a1  props x_pair a_pair Cons a1_xs a2_s conjoin_clist_xs clist_in_cptn
            conjoin_map clist_map by blast         
         then have "(\<Gamma>, c) \<in> par_cptn" using  a1 a2  props x_pair a_pair Cons a1_xs a2_s
         unfolding par_cp_def by simp          
         thus "x\<in>par_cp \<Gamma> xs s"  
           using a1 a2  props x_pair a_pair Cons a1_xs a2_s
         unfolding par_cp_def conjoin_def  same_length_def same_program_def same_state_def same_functions_def compat_label_def 
           by simp          
       qed
     }
     thus ?thesis using a1 a2 by auto  
   qed
  } 
qed



lemma one_iff_aux_only_if:"xs\<noteq>[] \<Longrightarrow>  
 (par_cp \<Gamma> (xs) s = {(\<Gamma>1,c). \<exists>clist. (length clist)=(length xs) \<and>
 (\<forall>i<length clist. clist!i \<in> cp \<Gamma> (xs!i) s) \<and> (\<Gamma>,c) \<propto> clist \<and> \<Gamma>1=\<Gamma>}) \<Longrightarrow>
(\<forall>ys. ((\<Gamma>,((xs, s)#ys)) \<in> par_cptn) = 
 (\<exists>clist. length clist= length xs \<and> 
 ((\<Gamma>,(xs, s)#ys) \<propto> map (\<lambda>i. (\<Gamma>,(fst i,s)#(snd i))) (zip xs clist)) \<and> 
 (\<forall>i<length xs. (\<Gamma>,(xs!i,s)#(clist!i)) \<in> cptn)))"
proof
  fix ys
  assume a1: "xs\<noteq>[]"
  assume a2: "par_cp \<Gamma> xs s =
          {(\<Gamma>1, c).
           \<exists>clist.
              length clist = length xs \<and>
              (\<forall>i<length clist.
                  clist ! i \<in> cp \<Gamma> (xs ! i) s) \<and>
              (\<Gamma>, c) \<propto> clist \<and> \<Gamma>1 = \<Gamma>}"
  from a1 a2 show
  "((\<Gamma>, (xs, s) # ys) \<in> par_cptn) =
          (\<exists>clist.
              length clist = length xs \<and>
              (\<Gamma>,
               (xs, s) #
               ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                       (zip xs clist) \<and>
              (\<forall>i<length xs.
                  (\<Gamma>, (xs ! i, s) # clist ! i) \<in> cptn))"
  proof auto
    {assume a3:"(\<Gamma>, (xs, s) # ys) \<in> par_cptn"
     then show "\<exists>clist.
       length clist = length xs \<and>
       (\<Gamma>,
        (xs, s) #
        ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                (zip xs clist) \<and>
       (\<forall>i<length xs. (\<Gamma>, (xs ! i, s) # clist ! i) \<in> cptn)"
       using a1 a2 by (simp add: aux_onlyif)
    }
    {fix clist ::"(('a, 'b, 'c, 'd) LanguageCon.com \<times>
             ('a, 'c) xstate) list list"
    assume a3: "length clist = length xs"
    assume a4:"(\<Gamma>, (xs, s) # ys) \<propto> 
               map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                (zip xs clist)"
    assume a5: "\<forall>i<length xs. (\<Gamma>, (xs ! i, s) # clist ! i)
                     \<in> cptn"
    show "(\<Gamma>, (xs, s) # ys) \<in> par_cptn" 
    using a3 a4 a5 using aux_if by blast 
    }
  qed
qed

lemma one_iff_aux: "xs\<noteq>[] \<Longrightarrow> (\<forall>ys. ((\<Gamma>,((xs, s)#ys)) \<in> par_cptn) = 
 (\<exists>clist. length clist= length xs \<and> 
 ((\<Gamma>,(xs, s)#ys) \<propto> map (\<lambda>i. (\<Gamma>,(fst i,s)#(snd i))) (zip xs clist)) \<and> 
 (\<forall>i<length xs. (\<Gamma>,(xs!i,s)#(clist!i)) \<in> cptn))) = 
 (par_cp \<Gamma> (xs) s = {(\<Gamma>1,c). \<exists>clist. (length clist)=(length xs) \<and>
 (\<forall>i<length clist. clist!i \<in> cp \<Gamma> (xs!i) s) \<and> (\<Gamma>,c) \<propto> clist \<and> \<Gamma>1=\<Gamma>})"
proof 
  assume a1:"xs\<noteq>[]"
  {assume a2:"(\<forall>ys. ((\<Gamma>,((xs, s)#ys)) \<in> par_cptn) = 
   (\<exists>clist. length clist= length xs \<and> 
   ((\<Gamma>,(xs, s)#ys) \<propto> map (\<lambda>i. (\<Gamma>,(fst i,s)#(snd i))) (zip xs clist)) \<and> 
   (\<forall>i<length xs. (\<Gamma>,(xs!i,s)#(clist!i)) \<in> cptn)))"
    then show "(par_cp \<Gamma> (xs) s = {(\<Gamma>1,c). \<exists>clist. (length clist)=(length xs) \<and>
   (\<forall>i<length clist. clist!i \<in> cp \<Gamma> (xs!i) s) \<and> (\<Gamma>,c) \<propto> clist \<and> \<Gamma>1=\<Gamma>})"
    by (auto simp add: a1 a2 one_iff_aux_if)
  }
  {assume a2:"(par_cp \<Gamma> (xs) s = {(\<Gamma>1,c). \<exists>clist. (length clist)=(length xs) \<and>
   (\<forall>i<length clist. clist!i \<in> cp \<Gamma> (xs!i) s) \<and> (\<Gamma>,c) \<propto> clist \<and> \<Gamma>1=\<Gamma>})"    
    then show "(\<forall>ys. ((\<Gamma>,((xs, s)#ys)) \<in> par_cptn) = 
   (\<exists>clist. length clist= length xs \<and> 
   ((\<Gamma>,(xs, s)#ys) \<propto> map (\<lambda>i. (\<Gamma>,(fst i,s)#(snd i))) (zip xs clist)) \<and> 
   (\<forall>i<length xs. (\<Gamma>,(xs!i,s)#(clist!i)) \<in> cptn)))"
   by (auto simp add: a1 a2 one_iff_aux_only_if)
  }
qed
  


theorem one: 
"xs\<noteq>[] \<Longrightarrow>  
 par_cp \<Gamma> xs s = 
    {(\<Gamma>1,c). \<exists>clist. (length clist)=(length xs) \<and> 
             (\<forall>i<length clist. (clist!i) \<in> cp \<Gamma> (xs!i) s) \<and> 
             (\<Gamma>,c) \<propto> clist \<and> \<Gamma>1=\<Gamma>}"

apply(frule one_iff_aux)
apply(drule sym)
apply(erule iffD2)
apply clarify
apply(rule iffI) 
 apply(erule aux_onlyif)
apply clarify
apply(force intro:aux_if)
done

(************************************************************************ *)
(* subsection {* Equivalence between Small-Step and Big-Step Semantics *} *)
(* ************************************************************************ *)
 
(* 

?\<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Seq ?c1.0 ?c2.0, ?s) \<rightarrow>
       (LanguageCon.com.Seq ?c1' ?c2.0,
        ?s') \<Longrightarrow>
(?\<Gamma>\<turnstile>\<^sub>c (?c1.0, ?s) \<rightarrow> (?c1', ?s') \<Longrightarrow> ?P) \<Longrightarrow>
?P

lemma 
   assumes 
           step_a: "\<Gamma>\<turnstile>\<^sub>c(Await b c, Normal s) \<rightarrow> (t,u)"
   shows step_await_step_c:"(\<Gamma>\<^sub>\<not>\<^sub>a)\<turnstile>(c, Normal s) \<rightarrow>\<^sup>* (sequential t,u)" 
using step_a
proof cases
  fix t1
  assume
      "(t, u) = (Skip, t1)" "s \<in> b" "\<Gamma>\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> t1" "\<forall>t'. t1 \<noteq> Abrupt t'"
  thus ?thesis 
   by (cases u) 
   (auto intro: exec_impl_steps_Fault exec_impl_steps_Normal exec_impl_steps_Stuck)
next
  fix t1
  assume "(t, u) = (Throw, Normal t1)" "s \<in> b" "\<Gamma>\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> Abrupt t1"
  thus ?thesis by (simp add: exec_impl_steps_Normal_Abrupt)
qed

lemma 
   assumes (* exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t" and
           b: "s \<in> b" and *)
           step_a: "\<Gamma>\<turnstile>\<^sub>c(Await b c, Normal s) \<rightarrow> u"
   shows step_await_final1:"final u"
using step_a 
proof cases
  case  (1 t) thus "final u"  by (simp add: final_def)
next
  case (2 t)
  thus "final u" by (simp add: exec_impl_steps_Normal_Abrupt final_def)
qed

lemma step_Abrupt_end: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')"
  shows "s'=Abrupt x \<Longrightarrow> s=Abrupt x"
using step
by induct auto


lemma step_Stuck_end: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')"
  shows "s'=Stuck \<Longrightarrow> 
          s=Stuck \<or> 
          (\<exists>r x. redex c\<^sub>1 = Spec r \<and> s=Normal x \<and> (\<forall>t. (x,t)\<notin>r)) \<or> 
          (\<exists>p x. redex c\<^sub>1=  Call p \<and> s=Normal x \<and> \<Gamma> p = None) \<or>
          (\<exists>b c x.  redex c\<^sub>1 = Await b c \<and> s=Normal x \<and> x \<in> b \<and> \<Gamma>\<turnstile>\<langle>c,s\<rangle>\<Rightarrow>s')"
using step
by induct auto

lemma step_Fault_end: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')"
  shows "s'=Fault f \<Longrightarrow> 
          s=Fault f \<or> 
          (\<exists>g c x.  redex c\<^sub>1 = Guard f g c \<and> s=Normal x \<and> x \<notin> g) \<or>
          (\<exists>b c1 x.  redex c\<^sub>1 = Await b c1 \<and> s=Normal x \<and> x \<in> b \<and> \<Gamma>\<turnstile>\<langle>c1,s\<rangle>\<Rightarrow>s')"
using step 
by induct auto



(* ************************************************************************ *)
subsection {* Infinite Computations: @{text "\<Gamma>\<turnstile>(c, s) \<rightarrow> \<dots>(\<infinity>)"}*}
(* ************************************************************************ *)

definition inf_c:: "('s,'p,'f,'e) body \<Rightarrow> ('s,'p,'f,'e) config \<Rightarrow> bool"
 ("_\<turnstile>\<^sub>c _ \<rightarrow> \<dots>'(\<infinity>')" [60,80] 100) where
"\<Gamma>\<turnstile>\<^sub>c cfg \<rightarrow> \<dots>(\<infinity>) \<equiv> (\<exists>f. f (0::nat) = cfg \<and> (\<forall>i. \<Gamma>\<turnstile>\<^sub>cf i \<rightarrow> f (i+1)))" 

lemma not_infI: "\<lbrakk>\<And>f. \<lbrakk>f 0 = cfg; \<And>i. \<Gamma>\<turnstile>\<^sub>cf i \<rightarrow> f (Suc i)\<rbrakk> \<Longrightarrow> False\<rbrakk>  
                \<Longrightarrow> \<not>\<Gamma>\<turnstile>\<^sub>c cfg \<rightarrow> \<dots>(\<infinity>)"
  by (auto simp add: inf_c_def)

(* ************************************************************************ *)
subsection {* Equivalence between Termination and the Absence of Infinite Computations*}
(* ************************************************************************ *)


lemma step_preserves_termination: 
  assumes step: "\<Gamma>\<turnstile>(c,s) \<rightarrow> (c',s')"
  shows "\<Gamma>\<turnstile>c\<down>s \<Longrightarrow> \<Gamma>\<turnstile>c'\<down>s'"  
using step
proof (induct)
  case Basic thus ?case by (fastforce intro: terminates.intros)
next
  case Spec thus ?case by (fastforce intro: terminates.intros)
next
  case SpecStuck thus ?case by (fastforce intro: terminates.intros)
next
  case Guard thus ?case 
    by (fastforce intro: terminates.intros elim: terminates_Normal_elim_cases)
next
  case GuardFault thus ?case by (fastforce intro: terminates.intros)
next
  case (Seq c\<^sub>1 s c\<^sub>1' s' c\<^sub>2) thus ?case
    apply (cases s)
    apply     (cases s')
    apply         (fastforce intro: terminates.intros step_extend 
                    elim: terminates_Normal_elim_cases)
    apply (fastforce intro: terminates.intros dest: step_Abrupt_prop 
      step_Fault_prop step_Stuck_prop)+
    done
next
  case (SeqSkip c\<^sub>2 s) 
  thus ?case 
    apply (cases s)
    apply (fastforce intro: terminates.intros exec.intros
            elim: terminates_Normal_elim_cases )+
    done
next
  case (SeqThrow c\<^sub>2 s) 
  thus ?case 
    by (fastforce intro: terminates.intros exec.intros
            elim: terminates_Normal_elim_cases )
next
  case CondTrue 
  thus ?case 
    by (fastforce intro: terminates.intros exec.intros
            elim: terminates_Normal_elim_cases )
next
  case CondFalse 
  thus ?case 
    by (fastforce intro: terminates.intros 
            elim: terminates_Normal_elim_cases )
next
  case WhileTrue
  thus ?case 
    by (fastforce intro: terminates.intros 
            elim: terminates_Normal_elim_cases )
next
  case WhileFalse 
  thus ?case 
    by (fastforce intro: terminates.intros 
            elim: terminates_Normal_elim_cases )
next
  case Call 
  thus ?case 
    by (fastforce intro: terminates.intros 
            elim: terminates_Normal_elim_cases )
next
  case CallUndefined
  thus ?case 
    by (fastforce intro: terminates.intros 
            elim: terminates_Normal_elim_cases )
next
  case DynCom
  thus ?case 
    by (fastforce intro: terminates.intros 
            elim: terminates_Normal_elim_cases )
next
  case (Catch c\<^sub>1 s c\<^sub>1' s' c\<^sub>2) thus ?case
    apply (cases s)
    apply     (cases s')
    apply         (fastforce intro: terminates.intros step_extend 
                    elim: terminates_Normal_elim_cases)
    apply (fastforce intro: terminates.intros dest: step_Abrupt_prop 
      step_Fault_prop step_Stuck_prop)+
    done
next
  case CatchThrow
  thus ?case 
   by (fastforce intro: terminates.intros exec.intros
            elim: terminates_Normal_elim_cases )
next
  case (CatchSkip c\<^sub>2 s) 
  thus ?case 
    by (cases s) (fastforce intro: terminates.intros)+
next
  case FaultProp thus ?case by (fastforce intro: terminates.intros)
next
  case StuckProp thus ?case by (fastforce intro: terminates.intros)
next
  case AbruptProp thus ?case by (fastforce intro: terminates.intros)
next 
  case Await thus ?case using terminates_Skip' by blast 
next 
  case AwaitAbrupt thus ?case by (fastforce intro: terminates.intros)
qed

lemma steps_preserves_termination: 
  assumes steps: "\<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* (c',s')"
  shows "\<Gamma>\<turnstile>c\<down>s \<Longrightarrow> \<Gamma>\<turnstile>c'\<down>s'"
using steps
proof (induct rule: rtranclp_induct2 [consumes 1, case_names Refl Trans])
  case Refl thus ?case  .
next
  case Trans
  thus ?case
    by (blast dest: step_preserves_termination)
qed

ML {*
  ML_Thms.bind_thm ("tranclp_induct2", Split_Rule.split_rule @{context}
    (Rule_Insts.read_instantiate @{context}
      [((("a", 0), Position.none), "(aa,ab)"), ((("b", 0), Position.none), "(ba,bb)")] []
      @{thm tranclp_induct}));
*}

thm tranclp_induct2 tranclp_induct

lemma steps_preserves_termination': 
  assumes steps: "\<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>+ (c',s')"
  shows "\<Gamma>\<turnstile>c\<down>s \<Longrightarrow> \<Gamma>\<turnstile>c'\<down>s'"
using steps
proof (induct rule: tranclp_induct2 [consumes 1, case_names Step Trans])
  case Step thus ?case by (blast intro: step_preserves_termination)
next
  case Trans
  thus ?case
    by (blast dest: step_preserves_termination)
qed



definition head_com:: "('s,'p,'f,'e) com \<Rightarrow> ('s,'p,'f,'e) com"
where
"head_com c =
  (case c of
     Seq c\<^sub>1 c\<^sub>2 \<Rightarrow> c\<^sub>1
   | Catch c\<^sub>1 c\<^sub>2 \<Rightarrow> c\<^sub>1
   | _ \<Rightarrow> c)"

  
definition head:: "('s,'p,'f,'e) config \<Rightarrow> ('s,'p,'f,'e) config"
  where "head cfg = (head_com (fst cfg), snd cfg)"

lemma le_Suc_cases: "\<lbrakk>\<And>i. \<lbrakk>i < k\<rbrakk> \<Longrightarrow> P i; P k\<rbrakk> \<Longrightarrow> \<forall>i<(Suc k). P i"
  apply clarify
  apply (case_tac "i=k")
  apply auto
  done

lemma redex_Seq_False: "\<And>c' c''. (redex c = Seq c'' c') = False"
  by (induct c) auto

lemma redex_Catch_False: "\<And>c' c''. (redex c = Catch c'' c') = False"
  by (induct c) auto


lemma infinite_computation_extract_head_Seq:
  assumes inf_comp: "\<forall>i::nat. \<Gamma>\<turnstile>f i \<rightarrow> f (i+1)"
  assumes f_0: "f 0 = (Seq c\<^sub>1 c\<^sub>2,s)"
  assumes not_fin: "\<forall>i<k. \<not> final (head (f i))"
  shows "\<forall>i<k. (\<exists>c' s'. f (i + 1) = (Seq c' c\<^sub>2, s')) \<and>  
               \<Gamma>\<turnstile>head (f i) \<rightarrow> head (f (i+1))"
        (is "\<forall>i<k. ?P i")
using not_fin
proof (induct k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have not_fin_Suc: 
    "\<forall>i<Suc k. \<not> final (head (f i))" by fact
  from this[rule_format] have not_fin_k: 
    "\<forall>i<k. \<not> final (head (f i))" 
    apply clarify
    apply (subgoal_tac "i < Suc k")
    apply blast
    apply simp
    done

  from Suc.hyps [OF this]
  have hyp: "\<forall>i<k. (\<exists>c' s'. f (i + 1) = (Seq c' c\<^sub>2, s')) \<and> 
                   \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))".
  show ?case
  proof (rule le_Suc_cases)
    fix i 
    assume "i < k"
    then show "?P i"
      by (rule hyp [rule_format])
  next
    show "?P k"
    proof -
      from hyp [rule_format, of "k - 1"] f_0
      obtain c' fs' L' s' where  f_k: "f k = (Seq c' c\<^sub>2, s')"
        by (cases k) auto
      from inf_comp [rule_format, of k] f_k
      have "\<Gamma>\<turnstile>(Seq c' c\<^sub>2, s') \<rightarrow> f (k + 1)"
        by simp
      moreover
      from not_fin_Suc [rule_format, of k] f_k
      have "\<not> final (c',s')"
        by (simp add: final_def head_def head_com_def)
      ultimately
      obtain c'' s'' where
         "\<Gamma>\<turnstile>(c', s') \<rightarrow> (c'', s'')" and
         "f (k + 1) = (Seq c'' c\<^sub>2, s'')"
        by cases (auto simp add: redex_Seq_False final_def)
      with f_k
      show ?thesis
        by (simp add: head_def head_com_def)
    qed
  qed
qed

lemma infinite_computation_extract_head_Catch:
  assumes inf_comp: "\<forall>i::nat. \<Gamma>\<turnstile>f i \<rightarrow> f (i+1)"
  assumes f_0: "f 0 = (Catch c\<^sub>1 c\<^sub>2,s)"
  assumes not_fin: "\<forall>i<k. \<not> final (head (f i))"
  shows "\<forall>i<k. (\<exists>c' s'. f (i + 1) = (Catch c' c\<^sub>2, s')) \<and>  
               \<Gamma>\<turnstile>head (f i) \<rightarrow> head (f (i+1))"
        (is "\<forall>i<k. ?P i")
using not_fin
proof (induct k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have not_fin_Suc: 
    "\<forall>i<Suc k. \<not> final (head (f i))" by fact
  from this[rule_format] have not_fin_k: 
    "\<forall>i<k. \<not> final (head (f i))" 
    apply clarify
    apply (subgoal_tac "i < Suc k")
    apply blast
    apply simp
    done

  from Suc.hyps [OF this]
  have hyp: "\<forall>i<k. (\<exists>c' s'. f (i + 1) = (Catch c' c\<^sub>2, s')) \<and> 
                   \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))".
  show ?case
  proof (rule le_Suc_cases)
    fix i 
    assume "i < k"
    then show "?P i"
      by (rule hyp [rule_format])
  next
    show "?P k"
    proof -
      from hyp [rule_format, of "k - 1"] f_0
      obtain c' fs' L' s' where  f_k: "f k = (Catch c' c\<^sub>2, s')"
        by (cases k) auto
      from inf_comp [rule_format, of k] f_k
      have "\<Gamma>\<turnstile>(Catch c' c\<^sub>2, s') \<rightarrow> f (k + 1)"
        by simp
      moreover
      from not_fin_Suc [rule_format, of k] f_k
      have "\<not> final (c',s')"
        by (simp add: final_def head_def head_com_def)
      ultimately
      obtain c'' s'' where
         "\<Gamma>\<turnstile>(c', s') \<rightarrow> (c'', s'')" and
         "f (k + 1) = (Catch c'' c\<^sub>2, s'')"
        by cases (auto simp add: redex_Catch_False final_def)+
      with f_k
      show ?thesis
        by (simp add: head_def head_com_def)
    qed
  qed
qed

lemma no_inf_Throw: "\<not> \<Gamma>\<turnstile>(Throw,s) \<rightarrow> \<dots>(\<infinity>)"
proof 
  assume "\<Gamma>\<turnstile> (Throw, s) \<rightarrow> \<dots>(\<infinity>)"
  then obtain f where
    step [rule_format]: "\<forall>i::nat. \<Gamma>\<turnstile>f i \<rightarrow> f (i+1)" and
    f_0: "f 0 = (Throw, s)"
    by (auto simp add: inf_def)
  from step [of 0, simplified f_0] step [of 1]
  show False
    by cases (auto elim: step_elim_cases)
qed

lemma split_inf_Seq: 
  assumes inf_comp: "\<Gamma>\<turnstile>(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow> \<dots>(\<infinity>)"
  shows "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow> \<dots>(\<infinity>) \<or> 
         (\<exists>s'. \<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow>\<^sup>* (Skip,s') \<and> \<Gamma>\<turnstile>(c\<^sub>2,s') \<rightarrow> \<dots>(\<infinity>))"
proof -
  from inf_comp obtain f where
    step: "\<forall>i::nat. \<Gamma>\<turnstile>f i \<rightarrow> f (i+1)" and
    f_0: "f 0 = (Seq c\<^sub>1 c\<^sub>2, s)"
    by (auto simp add: inf_def)
  from f_0 have head_f_0: "head (f 0) = (c\<^sub>1,s)" 
    by (simp add: head_def head_com_def)
  show ?thesis
  proof (cases "\<exists>i. final (head (f i))")
    case True
    def k\<equiv>"(LEAST i. final (head (f i)))"
    have less_k: "\<forall>i<k. \<not> final (head (f i))"
      apply (intro allI impI)
      apply (unfold k_def)
      apply (drule not_less_Least)
      apply auto
      done
    from infinite_computation_extract_head_Seq [OF step f_0 this]
    obtain step_head: "\<forall>i<k. \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))" and
           conf: "\<forall>i<k. (\<exists>c' s'. f (i + 1) = (Seq c' c\<^sub>2, s'))"
      by blast 
    from True
    have final_f_k: "final (head (f k))"
      apply -
      apply (erule exE)
      apply (drule LeastI)
      apply (simp add: k_def)
      done
    moreover
    from f_0 conf [rule_format, of "k - 1"]
    obtain c' s' where f_k: "f k = (Seq c' c\<^sub>2,s')"
      by (cases k) auto
    moreover
    from step_head have steps_head: "\<Gamma>\<turnstile>head (f 0) \<rightarrow>\<^sup>* head (f k)"
    proof (induct k)
      case 0 thus ?case by simp
    next
      case (Suc m)
      have step: "\<forall>i<Suc m. \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))" by fact
      hence "\<forall>i<m. \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))"
        by auto
      hence "\<Gamma>\<turnstile> head (f 0) \<rightarrow>\<^sup>*  head (f m)"
        by (rule Suc.hyps)
      also from step [rule_format, of m]
      have "\<Gamma>\<turnstile> head (f m) \<rightarrow> head (f (m + 1))" by simp
      finally show ?case by simp
    qed
    {
      assume f_k: "f k = (Seq Skip c\<^sub>2, s')"
      with steps_head
      have "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow>\<^sup>* (Skip,s')"
        using head_f_0
        by (simp add: head_def head_com_def)
      moreover
      from step [rule_format, of k] f_k
      obtain "\<Gamma>\<turnstile>(Seq Skip c\<^sub>2,s') \<rightarrow> (c\<^sub>2,s')" and
        f_Suc_k: "f (k + 1) = (c\<^sub>2,s')"
        by (fastforce elim: step.cases intro: step.intros)
      def g\<equiv>"\<lambda>i. f (i + (k + 1))"
      from f_Suc_k
      have g_0: "g 0 = (c\<^sub>2,s')"
        by (simp add: g_def)
      from step
      have "\<forall>i. \<Gamma>\<turnstile>g i \<rightarrow> g (i + 1)"
        by (simp add: g_def)
      with g_0 have "\<Gamma>\<turnstile>(c\<^sub>2,s') \<rightarrow> \<dots>(\<infinity>)"
        by (auto simp add: inf_def)
      ultimately
      have ?thesis
        by auto
    }
    moreover
    {
      fix x
      assume s': "s'=Normal x" and f_k: "f k = (Seq Throw c\<^sub>2, s')"
      from step [rule_format, of k] f_k s'
      obtain "\<Gamma>\<turnstile>(Seq Throw c\<^sub>2,s') \<rightarrow> (Throw,s')" and
        f_Suc_k: "f (k + 1) = (Throw,s')"
        by (fastforce elim: step_elim_cases intro: step.intros)
      def g\<equiv>"\<lambda>i. f (i + (k + 1))"
      from f_Suc_k
      have g_0: "g 0 = (Throw,s')"
        by (simp add: g_def)
      from step
      have "\<forall>i. \<Gamma>\<turnstile>g i \<rightarrow> g (i + 1)"
        by (simp add: g_def)
      with g_0 have "\<Gamma>\<turnstile>(Throw,s') \<rightarrow> \<dots>(\<infinity>)"
        by (auto simp add: inf_def)
      with no_inf_Throw
      have ?thesis
        by auto
    }
    ultimately 
    show ?thesis
      by (auto simp add: final_def head_def head_com_def)
  next
    case False
    then have not_fin: "\<forall>i. \<not> final (head (f i))"
      by blast
    have "\<forall>i. \<Gamma>\<turnstile>head (f i) \<rightarrow> head (f (i + 1))"
    proof 
      fix k
      from not_fin 
      have "\<forall>i<(Suc k). \<not> final (head (f i))"
        by simp
      
      from infinite_computation_extract_head_Seq [OF step f_0 this ]
      show "\<Gamma>\<turnstile> head (f k) \<rightarrow> head (f (k + 1))" by simp
    qed
    with head_f_0 have "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow> \<dots>(\<infinity>)"
      by (auto simp add: inf_def)
    thus ?thesis
      by simp
  qed
qed

lemma split_inf_Catch: 
  assumes inf_comp: "\<Gamma>\<turnstile>(Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow> \<dots>(\<infinity>)"
  shows "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow> \<dots>(\<infinity>) \<or> 
         (\<exists>s'. \<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow>\<^sup>* (Throw,Normal s') \<and> \<Gamma>\<turnstile>(c\<^sub>2,Normal s') \<rightarrow> \<dots>(\<infinity>))"
proof -
  from inf_comp obtain f where
    step: "\<forall>i::nat. \<Gamma>\<turnstile>f i \<rightarrow> f (i+1)" and
    f_0: "f 0 = (Catch c\<^sub>1 c\<^sub>2, s)"
    by (auto simp add: inf_def)
  from f_0 have head_f_0: "head (f 0) = (c\<^sub>1,s)" 
    by (simp add: head_def head_com_def)
  show ?thesis
  proof (cases "\<exists>i. final (head (f i))")
    case True
    def k\<equiv>"(LEAST i. final (head (f i)))"
    have less_k: "\<forall>i<k. \<not> final (head (f i))"
      apply (intro allI impI)
      apply (unfold k_def)
      apply (drule not_less_Least)
      apply auto
      done
    from infinite_computation_extract_head_Catch [OF step f_0 this]
    obtain step_head: "\<forall>i<k. \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))" and
           conf: "\<forall>i<k. (\<exists>c' s'. f (i + 1) = (Catch c' c\<^sub>2, s'))"
      by blast 
    from True
    have final_f_k: "final (head (f k))"
      apply -
      apply (erule exE)
      apply (drule LeastI)
      apply (simp add: k_def)
      done
    moreover
    from f_0 conf [rule_format, of "k - 1"]
    obtain c' s' where f_k: "f k = (Catch c' c\<^sub>2,s')"
      by (cases k) auto
    moreover
    from step_head have steps_head: "\<Gamma>\<turnstile>head (f 0) \<rightarrow>\<^sup>* head (f k)"
    proof (induct k)
      case 0 thus ?case by simp
    next
      case (Suc m)
      have step: "\<forall>i<Suc m. \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))" by fact
      hence "\<forall>i<m. \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))"
        by auto
      hence "\<Gamma>\<turnstile> head (f 0) \<rightarrow>\<^sup>*  head (f m)"
        by (rule Suc.hyps)
      also from step [rule_format, of m]
      have "\<Gamma>\<turnstile> head (f m) \<rightarrow> head (f (m + 1))" by simp
      finally show ?case by simp
    qed
    {
      assume f_k: "f k = (Catch Skip c\<^sub>2, s')"
      with steps_head
      have "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow>\<^sup>* (Skip,s')"
        using head_f_0
        by (simp add: head_def head_com_def)
      moreover
      from step [rule_format, of k] f_k
      obtain "\<Gamma>\<turnstile>(Catch Skip c\<^sub>2,s') \<rightarrow> (Skip,s')" and
        f_Suc_k: "f (k + 1) = (Skip,s')"
        by (fastforce elim: step.cases intro: step.intros)
      from step [rule_format, of "k+1", simplified f_Suc_k]
      have ?thesis
        by (rule no_step_final') (auto simp add: final_def)
    }
    moreover
    {
      fix x
      assume s': "s'=Normal x" and f_k: "f k = (Catch Throw c\<^sub>2, s')"
      with steps_head
      have "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow>\<^sup>* (Throw,s')"
        using head_f_0
        by (simp add: head_def head_com_def)
      moreover
      from step [rule_format, of k] f_k s'
      obtain "\<Gamma>\<turnstile>(Catch Throw c\<^sub>2,s') \<rightarrow> (c\<^sub>2,s')" and
        f_Suc_k: "f (k + 1) = (c\<^sub>2,s')"
        by (fastforce elim: step_elim_cases intro: step.intros)
      def g\<equiv>"\<lambda>i. f (i + (k + 1))"
      from f_Suc_k
      have g_0: "g 0 = (c\<^sub>2,s')"
        by (simp add: g_def)
      from step
      have "\<forall>i. \<Gamma>\<turnstile>g i \<rightarrow> g (i + 1)"
        by (simp add: g_def)
      with g_0 have "\<Gamma>\<turnstile>(c\<^sub>2,s') \<rightarrow> \<dots>(\<infinity>)"
        by (auto simp add: inf_def)
      ultimately
      have ?thesis
        using s'
        by auto
    }
    ultimately 
    show ?thesis
      by (auto simp add: final_def head_def head_com_def)
  next
    case False
    then have not_fin: "\<forall>i. \<not> final (head (f i))"
      by blast
    have "\<forall>i. \<Gamma>\<turnstile>head (f i) \<rightarrow> head (f (i + 1))"
    proof 
      fix k
      from not_fin 
      have "\<forall>i<(Suc k). \<not> final (head (f i))"
        by simp
      
      from infinite_computation_extract_head_Catch [OF step f_0 this ]
      show "\<Gamma>\<turnstile> head (f k) \<rightarrow> head (f (k + 1))" by simp
    qed
    with head_f_0 have "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow> \<dots>(\<infinity>)"
      by (auto simp add: inf_def)
    thus ?thesis
      by simp
  qed
qed

lemma Skip_no_step: "\<Gamma>\<turnstile>(Skip,s) \<rightarrow> cfg \<Longrightarrow> P"
  apply (erule no_step_final')
  apply (simp add: final_def)
  done

lemma not_inf_Stuck: "\<not> \<Gamma>\<turnstile>(c,Stuck) \<rightarrow> \<dots>(\<infinity>)"
proof (induct c)
  case Skip
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Skip, Stuck)" 
    from f_step [of 0] f_0
    show False
      by (auto elim: Skip_no_step)
  qed
next
  case (Basic g) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Basic g, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Spec r) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Spec r, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Seq c\<^sub>1 c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Stuck) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Seq [OF this] Seq.hyps
    show False
      by (auto dest: steps_Stuck_prop)
  qed
next
  case (Cond b c\<^sub>1 c\<^sub>2) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Cond b c\<^sub>1 c\<^sub>2, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (While b c) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (While b c, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Call p) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Call p, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (DynCom d) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (DynCom d, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Guard m g c)
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Guard m g c, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case Throw
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Throw, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Catch c\<^sub>1 c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Stuck) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Catch [OF this] Catch.hyps
    show False
      by (auto dest: steps_Stuck_prop)
  qed  
next 
  case (Await b c)
  show ?case 
   proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Await b c, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
qed

lemma not_inf_Fault: "\<not> \<Gamma>\<turnstile>(c,Fault x) \<rightarrow> \<dots>(\<infinity>)"
proof (induct c)
  case Skip
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Skip, Fault x)" 
    from f_step [of 0] f_0
    show False
      by (auto elim: Skip_no_step)
  qed
next
  case (Basic g) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Basic g, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Spec r) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Spec r, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Seq c\<^sub>1 c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Fault x) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Seq [OF this] Seq.hyps
    show False
      by (auto dest: steps_Fault_prop)
  qed
next
  case (Cond b c\<^sub>1 c\<^sub>2) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Cond b c\<^sub>1 c\<^sub>2, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (While b c) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (While b c, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Call p) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Call p, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (DynCom d) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (DynCom d, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Guard m g c)
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Guard m g c, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case Throw
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Throw, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Catch c\<^sub>1 c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Fault x) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Catch [OF this] Catch.hyps
    show False
      by (auto dest: steps_Fault_prop)
  qed  
next
  case (Await b c) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Await b c, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
qed

lemma not_inf_Abrupt: "\<not> \<Gamma>\<turnstile>(c,Abrupt s) \<rightarrow> \<dots>(\<infinity>)"
proof (induct c)
  case Skip
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Skip, Abrupt s)" 
    from f_step [of 0] f_0
    show False
      by (auto elim: Skip_no_step)
  qed
next
  case (Basic g) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Basic g, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Spec r) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Spec r, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Seq c\<^sub>1 c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Abrupt s) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Seq [OF this] Seq.hyps
    show False
      by (auto dest: steps_Abrupt_prop)
  qed
next
  case (Cond b c\<^sub>1 c\<^sub>2) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Cond b c\<^sub>1 c\<^sub>2, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (While b c) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (While b c, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Call p) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Call p, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (DynCom d) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (DynCom d, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Guard m g c)
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Guard m g c, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case Throw
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Throw, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Catch c\<^sub>1 c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Abrupt s) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Catch [OF this] Catch.hyps
    show False
      by (auto dest: steps_Abrupt_prop)
  qed  
case (Await b c) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Await b c, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
qed


theorem terminates_impl_no_infinite_computation:
  assumes termi: "\<Gamma>\<turnstile>c \<down> s"
  shows "\<not> \<Gamma>\<turnstile>(c,s) \<rightarrow> \<dots>(\<infinity>)"
using termi
proof (induct)
  case (Skip s) thus ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Skip, Normal s)" 
    from f_step [of 0] f_0
    show False
      by (auto elim: Skip_no_step)
  qed
next
  case (Basic g s) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Basic g, Normal s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Spec r s) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Spec r, Normal s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Guard s g c m)
  have g: "s \<in> g" by fact
  have hyp: "\<not> \<Gamma>\<turnstile> (c, Normal s) \<rightarrow> \<dots>(\<infinity>)" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Guard m g c, Normal s)" 
    from f_step [of 0] f_0  g
    have "f 1 = (c,Normal s)"
      by (fastforce elim: step_elim_cases)
    with f_step
    have "\<Gamma>\<turnstile> (c, Normal s) \<rightarrow> \<dots>(\<infinity>)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with hyp show False ..
  qed
next
  case (GuardFault s g m c)
  have g: "s \<notin> g" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Guard m g c, Normal s)" 
    from g f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Fault c m) 
  thus ?case
    by (rule not_inf_Fault)
next
  case (Seq c\<^sub>1 s c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Seq [OF this] Seq.hyps
    show False
      by (auto intro: steps_Skip_impl_exec)
  qed
next
  case (CondTrue s b c1 c2)
  have b: "s \<in> b" by fact
  have hyp_c1: "\<not> \<Gamma>\<turnstile> (c1, Normal s) \<rightarrow> \<dots>(\<infinity>)" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Cond b c1 c2, Normal s)" 
    from b f_step [of 0] f_0
    have "f 1 = (c1,Normal s)"
      by (auto elim: step_Normal_elim_cases)
    with f_step
    have "\<Gamma>\<turnstile> (c1, Normal s) \<rightarrow> \<dots>(\<infinity>)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with hyp_c1 show False by simp
  qed    
next
  case (CondFalse s b c2 c1)
  have b: "s \<notin> b" by fact
  have hyp_c2: "\<not> \<Gamma>\<turnstile> (c2, Normal s) \<rightarrow> \<dots>(\<infinity>)" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Cond b c1 c2, Normal s)" 
    from b f_step [of 0] f_0
    have "f 1 = (c2,Normal s)"
      by (auto elim: step_Normal_elim_cases)
    with f_step
    have "\<Gamma>\<turnstile> (c2, Normal s) \<rightarrow> \<dots>(\<infinity>)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with hyp_c2 show False by simp
  qed
next    
  case (WhileTrue s b c)
  have b: "s \<in> b" by fact
  have hyp_c: "\<not> \<Gamma>\<turnstile> (c, Normal s) \<rightarrow> \<dots>(\<infinity>)" by fact
  have hyp_w: "\<forall>s'. \<Gamma>\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> s' \<longrightarrow> 
                     \<Gamma>\<turnstile>While b c \<down> s' \<and> \<not> \<Gamma>\<turnstile> (While b c, s') \<rightarrow> \<dots>(\<infinity>)" by fact
  have not_inf_Seq: "\<not> \<Gamma>\<turnstile> (Seq c (While b c), Normal s) \<rightarrow> \<dots>(\<infinity>)"
  proof 
    assume "\<Gamma>\<turnstile> (Seq c (While b c), Normal s) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Seq [OF this] hyp_c hyp_w show False
      by (auto intro: steps_Skip_impl_exec)
  qed
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (While b c, Normal s) \<rightarrow> \<dots>(\<infinity>)"
    then obtain f where
      f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)" and
      f_0: "f 0 = (While b c, Normal s)" 
      by (auto simp add: inf_def)
    from f_step [of 0] f_0 b
    have "f 1 = (Seq c (While b c),Normal s)"
      by (auto elim: step_Normal_elim_cases)
    with f_step
    have "\<Gamma>\<turnstile> (Seq c (While b c), Normal s) \<rightarrow> \<dots>(\<infinity>)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with not_inf_Seq show False by simp
  qed
next
  case (WhileFalse s b c)
  have b: "s \<notin> b" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (While b c, Normal s)" 
    from b f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Call p bdy s)
  have bdy: "\<Gamma> p = Some bdy" by fact
  have hyp: "\<not> \<Gamma>\<turnstile> (bdy, Normal s) \<rightarrow> \<dots>(\<infinity>)" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Call p, Normal s)" 
    from bdy f_step [of 0] f_0
    have "f 1 = (bdy,Normal s)"
      by (auto elim: step_Normal_elim_cases)
    with f_step
    have "\<Gamma>\<turnstile> (bdy, Normal s) \<rightarrow> \<dots>(\<infinity>)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with hyp show False by simp
  qed    
next
  case (CallUndefined p s)
  have no_bdy: "\<Gamma> p = None" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Call p, Normal s)" 
    from no_bdy f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Stuck c)
  show ?case
    by (rule not_inf_Stuck)
next
  case (DynCom c s)
  have hyp: "\<not> \<Gamma>\<turnstile> (c s, Normal s) \<rightarrow> \<dots>(\<infinity>)" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (DynCom c, Normal s)" 
    from f_step [of 0] f_0
    have "f (Suc 0) = (c s, Normal s)"
      by (auto elim: step_elim_cases)
    with f_step have "\<Gamma>\<turnstile> (c s, Normal s) \<rightarrow> \<dots>(\<infinity>)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with hyp
    show False by simp
  qed
next (\<Gamma>,c) \<propto> clist
  case (Throw s) thus ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Throw, Normal s)" 
    from f_step [of 0] f_0
    show False
      by (auto elim: step_elim_cases)
  qed  
next
  case (Abrupt c)
  show ?case
    by (rule not_inf_Abrupt)
next
  case (Catch c\<^sub>1 s c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Catch [OF this] Catch.hyps
    show False
      by (auto intro: steps_Throw_impl_exec)
  qed
next
  case (AwaitTrue s b c)
  have b: "s \<in> b" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Await b c, Normal s)" 
    from b f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
qed


definition
 termi_call_steps :: "('s,'p,'f,'e) body \<Rightarrow> (('s \<times> 'p) \<times> ('s \<times> 'p))set"
where
"termi_call_steps \<Gamma> =
 {((t,q),(s,p)). \<Gamma>\<turnstile>Call p\<down>Normal s \<and> 
       (\<exists>c. \<Gamma>\<turnstile>(Call p,Normal s) \<rightarrow>\<^sup>+ (c,Normal t) \<and> redex c = Call q)}"


primrec subst_redex:: "('s,'p,'f,'e)com \<Rightarrow> ('s,'p,'f,'e)com \<Rightarrow> ('s,'p,'f,'e)com"
where
"subst_redex Skip c = c" |
"subst_redex (Basic f) c = c" |
"subst_redex (Spec r) c = c" |
"subst_redex (Seq c\<^sub>1 c\<^sub>2) c  = Seq (subst_redex c\<^sub>1 c) c\<^sub>2" |
"subst_redex (Cond b c\<^sub>1 c\<^sub>2) c = c" |
"subst_redex (While b c') c = c" |
"subst_redex (Await b c') c = c" |
"subst_redex (Call p) c = c" |
"subst_redex (DynCom d) c = c" |
"subst_redex (Guard f b c') c = c" |
"subst_redex (Throw) c = c" |
"subst_redex (Catch c\<^sub>1 c\<^sub>2) c = Catch (subst_redex c\<^sub>1 c) c\<^sub>2"

lemma subst_redex_redex:
  "subst_redex c (redex c) = c"
  by (induct c) auto

lemma redex_subst_redex: "redex (subst_redex c r) = redex r"
  by (induct c) auto
  
lemma step_redex':
  shows "\<Gamma>\<turnstile>(redex c,s) \<rightarrow> (r',s') \<Longrightarrow> \<Gamma>\<turnstile>(c,s) \<rightarrow> (subst_redex c r',s')"
by (induct c) (auto intro: step.Seq step.Catch)


lemma step_redex:
  shows "\<Gamma>\<turnstile>(r,s) \<rightarrow> (r',s') \<Longrightarrow> \<Gamma>\<turnstile>(subst_redex c r,s) \<rightarrow> (subst_redex c r',s')"
by (induct c) (auto intro: step.Seq step.Catch)

lemma steps_redex:
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>* (r', s')"
  shows "\<And>c. \<Gamma>\<turnstile>(subst_redex c r,s) \<rightarrow>\<^sup>* (subst_redex c r',s')"
using steps
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl 
  show "\<Gamma>\<turnstile> (subst_redex c r', s') \<rightarrow>\<^sup>* (subst_redex c r', s')"
    by simp
next
  case (Trans r s r'' s'')
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r'', s'')" by fact
  from step_redex [OF this]
  have "\<Gamma>\<turnstile> (subst_redex c r, s) \<rightarrow> (subst_redex c r'', s'')".
  also  
  have "\<Gamma>\<turnstile> (subst_redex c r'', s'') \<rightarrow>\<^sup>* (subst_redex c r', s')" by fact
  finally show ?case .
qed

ML {*
  ML_Thms.bind_thm ("trancl_induct2", Split_Rule.split_rule @{context}
    (Rule_Insts.read_instantiate @{context}
      [((("a", 0), Position.none), "(aa, ab)"), ((("b", 0), Position.none), "(ba, bb)")] []
      @{thm trancl_induct}));
*}

lemma steps_redex':
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>+ (r', s')"
  shows "\<And>c. \<Gamma>\<turnstile>(subst_redex c r,s) \<rightarrow>\<^sup>+ (subst_redex c r',s')"
using steps
proof (induct rule: tranclp_induct2 [consumes 1,case_names Step Trans])
  case (Step r' s')
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r', s')" by fact
  then have "\<Gamma>\<turnstile> (subst_redex c r, s) \<rightarrow> (subst_redex c r', s')"
    by (rule step_redex)
  then show "\<Gamma>\<turnstile> (subst_redex c r, s) \<rightarrow>\<^sup>+ (subst_redex c r', s')"..
next
  case (Trans r' s' r'' s'')
  have "\<Gamma>\<turnstile> (subst_redex c r, s) \<rightarrow>\<^sup>+ (subst_redex c r', s')" by fact
  also
  have "\<Gamma>\<turnstile> (r', s') \<rightarrow> (r'', s'')" by fact
  hence "\<Gamma>\<turnstile> (subst_redex c r', s') \<rightarrow> (subst_redex c r'', s'')"
    by (rule step_redex)
  finally show "\<Gamma>\<turnstile> (subst_redex c r, s) \<rightarrow>\<^sup>+ (subst_redex c r'', s'')" .
qed

primrec seq:: "(nat \<Rightarrow> ('s,'p,'f,'e)com) \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> ('s,'p,'f,'e)com"
where
"seq c p 0 = Call p" |
"seq c p (Suc i) = subst_redex (seq c p i) (c i)"


lemma renumber':
  assumes f: "\<forall>i. (a,f i) \<in> r\<^sup>* \<and> (f i,f(Suc i)) \<in> r" 
  assumes a_b: "(a,b) \<in> r\<^sup>*" 
  shows "b = f 0 \<Longrightarrow> (\<exists>f. f 0 = a \<and> (\<forall>i. (f i, f(Suc i)) \<in> r))"
using a_b
proof (induct rule: converse_rtrancl_induct [consumes 1])
  assume "b = f 0"
  with f show "\<exists>f. f 0 = b \<and> (\<forall>i. (f i, f (Suc i)) \<in> r)"
    by blast
next
  fix a z
  assume a_z: "(a, z) \<in> r" and "(z, b) \<in> r\<^sup>*" 
  assume "b = f 0 \<Longrightarrow> \<exists>f. f 0 = z \<and> (\<forall>i. (f i, f (Suc i)) \<in> r)"
         "b = f 0"
  then obtain f where f0: "f 0 = z" and seq: "\<forall>i. (f i, f (Suc i)) \<in> r"
    by iprover
  {
    fix i have "((\<lambda>i. case i of 0 \<Rightarrow> a | Suc i \<Rightarrow> f i) i, f i) \<in> r"
      using seq a_z f0
      by (cases i) auto
  }
  then
  show "\<exists>f. f 0 = a \<and> (\<forall>i. (f i, f (Suc i)) \<in> r)"
    by - (rule exI [where x="\<lambda>i. case i of 0 \<Rightarrow> a | Suc i \<Rightarrow> f i"],simp)
qed

lemma renumber:
 "\<forall>i. (a,f i) \<in> r\<^sup>* \<and> (f i,f(Suc i)) \<in> r 
 \<Longrightarrow> \<exists>f. f 0 = a \<and> (\<forall>i. (f i, f(Suc i)) \<in> r)"
  by (blast dest:renumber')

lemma lem:
  "\<forall>y. r\<^sup>+\<^sup>+ a y \<longrightarrow> P a \<longrightarrow> P y 
   \<Longrightarrow> ((b,a) \<in> {(y,x). P x \<and> r x y}\<^sup>+) = ((b,a) \<in> {(y,x). P x \<and> r\<^sup>+\<^sup>+ x y})"
apply(rule iffI)
 apply clarify
 apply(erule trancl_induct)
  apply blast
 apply(blast intro:tranclp_trans)
apply clarify
apply(erule tranclp_induct)
 apply blast
apply(blast intro:trancl_trans)
done

corollary terminates_impl_no_infinite_trans_computation:
 assumes terminates: "\<Gamma>\<turnstile>c\<down>s"
 shows "\<not>(\<exists>f. f 0 = (c,s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow>\<^sup>+ f(Suc i)))"
proof -
  have "wf({(y,x). \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow> y}\<^sup>+)"
  proof (rule wf_trancl)
    show "wf {(y, x). \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow> y}"
    proof (simp only: wf_iff_no_infinite_down_chain,clarify,simp)
      fix f
      assume "\<forall>i. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* f i \<and> \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
      hence "\<exists>f. f (0::nat) = (c,s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i))"
        by (rule renumber [to_pred])
      moreover from terminates_impl_no_infinite_computation [OF terminates]
      have "\<not> (\<exists>f. f (0::nat) = (c, s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)))"
        by (simp add: inf_def)
      ultimately show False
        by simp
    qed
  qed
  hence "\<not> (\<exists>f. \<forall>i. (f (Suc i), f i)
                 \<in> {(y, x). \<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow> y}\<^sup>+)"
    by (simp add: wf_iff_no_infinite_down_chain)
  thus ?thesis
  proof (rule contrapos_nn)
    assume "\<exists>f. f (0::nat) = (c, s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow>\<^sup>+ f (Suc i))"
    then obtain f where
      f0: "f 0 = (c, s)" and
      seq: "\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow>\<^sup>+ f (Suc i)"
      by iprover
    show 
      "\<exists>f. \<forall>i. (f (Suc i), f i) \<in> {(y, x). \<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow> y}\<^sup>+"
    proof (rule exI [where x=f],rule allI)
      fix i
      show "(f (Suc i), f i) \<in> {(y, x). \<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow> y}\<^sup>+"
      proof -   
        {
          fix i have "\<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* f i"
          proof (induct i)
            case 0 show "\<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* f 0"
              by (simp add: f0)
          next
            case (Suc n)
            have "\<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* f n"  by fact
            with seq show "\<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* f (Suc n)"
              by (blast intro: tranclp_into_rtranclp rtranclp_trans)
          qed
        }
        hence "\<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* f i"
          by iprover
        with seq have
          "(f (Suc i), f i) \<in> {(y, x). \<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow>\<^sup>+ y}"
          by clarsimp
        moreover 
        have "\<forall>y. \<Gamma>\<turnstile>f i \<rightarrow>\<^sup>+ y\<longrightarrow>\<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* f i\<longrightarrow>\<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* y"
          by (blast intro: tranclp_into_rtranclp rtranclp_trans)
        ultimately 
        show ?thesis 
          by (subst lem )
      qed
    qed
  qed
qed

theorem wf_termi_call_steps: "wf (termi_call_steps \<Gamma>)"
proof (simp only: termi_call_steps_def wf_iff_no_infinite_down_chain,
       clarify,simp)
  fix f
  assume inf: "\<forall>i. (\<lambda>(t, q) (s, p).
                \<Gamma>\<turnstile>Call p \<down> Normal s \<and>
                (\<exists>c. \<Gamma>\<turnstile> (Call p, Normal s) \<rightarrow>\<^sup>+ (c, Normal t) \<and> redex c = Call q))
             (f (Suc i)) (f i)"
  def s\<equiv>"\<lambda>i::nat. fst (f i)" 
  def p\<equiv>"\<lambda>i::nat. snd (f i)::'b"
  from inf
  have inf': "\<forall>i. \<Gamma>\<turnstile>Call (p i) \<down> Normal (s i) \<and>
               (\<exists>c. \<Gamma>\<turnstile> (Call (p i), Normal (s i)) \<rightarrow>\<^sup>+ (c, Normal (s (i+1))) \<and> 
                    redex c = Call (p (i+1)))"
    apply -
    apply (rule allI)
    apply (erule_tac x=i in allE)
    apply (auto simp add: s_def p_def)
    done
  show False
  proof -
    from inf'
    have "\<exists>c. \<forall>i. \<Gamma>\<turnstile>Call (p i) \<down> Normal (s i) \<and>
               \<Gamma>\<turnstile> (Call (p i), Normal (s i)) \<rightarrow>\<^sup>+ (c i, Normal (s (i+1))) \<and> 
                    redex (c i) = Call (p (i+1))"
      apply -
      apply (rule choice)
      by blast
    then obtain c where
      termi_c: "\<forall>i. \<Gamma>\<turnstile>Call (p i) \<down> Normal (s i)" and
      steps_c: "\<forall>i. \<Gamma>\<turnstile> (Call (p i), Normal (s i)) \<rightarrow>\<^sup>+ (c i, Normal (s (i+1)))" and
      red_c:   "\<forall>i. redex (c i) = Call (p (i+1))"
      by auto
    def g\<equiv>"\<lambda>i. (seq c (p 0) i,Normal (s i)::('a,'c) xstate)"
    from red_c [rule_format, of 0]
    have "g 0 = (Call (p 0), Normal (s 0))"
      by (simp add: g_def)
    moreover
    {
      fix i
      have "redex (seq c (p 0) i) = Call (p i)"
        by (induct i) (auto simp add: redex_subst_redex red_c)
      from this [symmetric]
      have "subst_redex (seq c (p 0) i) (Call (p i)) = (seq c (p 0) i)"
        by (simp add: subst_redex_redex)
    } note subst_redex_seq = this
    have "\<forall>i. \<Gamma>\<turnstile> (g i) \<rightarrow>\<^sup>+ (g (i+1))"
    proof 
      fix i
      from steps_c [rule_format, of i]
      have "\<Gamma>\<turnstile> (Call (p i), Normal (s i)) \<rightarrow>\<^sup>+ (c i, Normal (s (i + 1)))".
      from steps_redex' [OF this, of "(seq c (p 0) i)"]
      have "\<Gamma>\<turnstile> (subst_redex (seq c (p 0) i) (Call (p i)), Normal (s i)) \<rightarrow>\<^sup>+
                (subst_redex (seq c (p 0) i) (c i), Normal (s (i + 1)))" .
      hence "\<Gamma>\<turnstile> (seq c (p 0) i, Normal (s i)) \<rightarrow>\<^sup>+ 
                 (seq c (p 0) (i+1), Normal (s (i + 1)))"
        by (simp add: subst_redex_seq)
      thus "\<Gamma>\<turnstile> (g i) \<rightarrow>\<^sup>+ (g (i+1))"
        by (simp add: g_def)
    qed
    moreover
    from terminates_impl_no_infinite_trans_computation [OF termi_c [rule_format, of 0]]
    have "\<not> (\<exists>f. f 0 = (Call (p 0), Normal (s 0)) \<and> (\<forall>i. \<Gamma>\<turnstile> f i \<rightarrow>\<^sup>+ f (Suc i)))" .
    ultimately show False
      by auto
  qed
qed


lemma no_infinite_computation_implies_wf: 
  assumes not_inf: "\<not> \<Gamma>\<turnstile> (c, s) \<rightarrow> \<dots>(\<infinity>)"
  shows "wf {(c2,c1). \<Gamma> \<turnstile> (c,s) \<rightarrow>\<^sup>* c1 \<and> \<Gamma> \<turnstile> c1 \<rightarrow> c2}"
proof (simp only: wf_iff_no_infinite_down_chain,clarify, simp)
  fix f
  assume "\<forall>i. \<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* f i \<and> \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
  hence "\<exists>f. f 0 = (c, s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i))"
    by (rule renumber [to_pred])
  moreover from not_inf
  have "\<not> (\<exists>f. f 0 = (c, s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)))"
    by (simp add: inf_def)
  ultimately show False
    by simp
qed

lemma not_final_Stuck_step: "\<not> final (c,Stuck) \<Longrightarrow> \<exists>c' s'. \<Gamma>\<turnstile> (c, Stuck) \<rightarrow> (c',s')"
by (induct c) (fastforce intro: step.intros simp add: final_def)+

lemma not_final_Abrupt_step: 
  "\<not> final (c,Abrupt s) \<Longrightarrow> \<exists>c' s'. \<Gamma>\<turnstile> (c, Abrupt s) \<rightarrow> (c',s')"
by (induct c) (fastforce intro: step.intros simp add: final_def)+

lemma not_final_Fault_step: 
  "\<not> final (c,Fault f) \<Longrightarrow> \<exists>c' s'. \<Gamma>\<turnstile> (c, Fault f) \<rightarrow> (c',s')"
by (induct c) (fastforce intro: step.intros simp add: final_def)+

lemma not_final_Normal_step: 
  "\<not> final (c,Normal s) \<and> ((\<exists>b c1. redex c = Await b c1) \<longrightarrow> \<Gamma>\<turnstile>c \<down> Normal s) \<Longrightarrow> \<exists>c' s'. \<Gamma>\<turnstile> (c, Normal s) \<rightarrow> (c',s')"
proof (induct c) 
  case Skip thus ?case by (simp add: final_def)
next
  case Basic thus ?case by (meson step.Basic)
next
  case (Spec r)
  thus ?case by (meson step.Spec step.SpecStuck)    
next
  case (Seq c\<^sub>1 c\<^sub>2)
  thus ?case by (metis SeqSkip SeqThrow final_def fst_conv redex.simps(4) step.Seq terminates_Normal_elim_cases(5))
next
  case (Cond b c1 c2)
  show ?case
    by (cases "s \<in> b") (fastforce intro: step.intros)+
next
  case (While b c)
  show ?case
    by (cases "s \<in> b") (fastforce intro: step.intros)+
next
  case (Call p)
  show ?case
  by (cases "\<Gamma> p") (fastforce intro: step.intros)+
next
  case DynCom thus ?case by (fastforce intro: step.intros)
next
  case (Guard f g c)
  show ?case
    by (cases "s \<in> g") (fastforce intro: step.intros)+
next
  case Throw
  thus ?case by (fastforce intro: step.intros simp add: final_def)
next
  case (Catch c\<^sub>1 c\<^sub>2)
  thus ?case
    by (cases "final (c\<^sub>1,Normal s)") (fastforce intro: step.intros elim: terminates_Normal_elim_cases simp add: final_def)+
next
  case (Await b c) 
  then obtain ba c1 where x:"(\<exists>ba c1. redex (Await b c) = Await ba c1)" by simp
  then have "\<Gamma>\<turnstile>Await b c \<down> Normal s" using x Await.prems by blast 
  also have "s \<in> b" by (meson `\<Gamma>\<turnstile>Await b c \<down> Normal s` terminates_Normal_elim_cases(12))
  moreover have "\<exists>t. \<Gamma>\<turnstile>\<langle>c, Normal s\<rangle> \<Rightarrow> t" by (meson calculation terminates_Normal_elim_cases(12) terminates_implies_exec) 
  ultimately show ?case using AwaitAbrupt  step.Await by fastforce
qed

lemma final_termi:
"final (c,s) \<Longrightarrow> \<Gamma>\<turnstile>c\<down>s"
  by (cases s) (auto simp add: final_def terminates.intros)

lemma split_computation: 
assumes steps: "\<Gamma>\<turnstile> (c, s) \<rightarrow>\<^sup>* (c\<^sub>f, s\<^sub>f)"
assumes not_final: "\<not> final (c,s)"
assumes final: "final (c\<^sub>f,s\<^sub>f)"
shows "\<exists>c' s'. \<Gamma>\<turnstile> (c, s) \<rightarrow> (c',s') \<and> \<Gamma>\<turnstile> (c', s') \<rightarrow>\<^sup>* (c\<^sub>f, s\<^sub>f)"
using steps not_final final
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case by simp
next
  case (Trans c s c' s')
  thus ?case by auto
qed


lemma wf_implies_termi_reach_step_case:
assumes hyp: "\<And>c' s'. \<Gamma>\<turnstile> (c, Normal s) \<rightarrow> (c', s')\<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" and
        hyp1:"(\<And>b c1. (redex c = Await b c1) \<Longrightarrow> \<Gamma>\<turnstile>c1 \<down> Normal s \<and> s\<in>b)"
shows "\<Gamma>\<turnstile>c \<down> Normal s"
using hyp hyp1
proof (induct c)
  case Skip show ?case by (fastforce intro: terminates.intros)
next
  case Basic show ?case by (fastforce intro: terminates.intros)
next
  case (Spec r)
  show ?case
    by (cases "\<exists>t. (s,t)\<in>r") (fastforce intro: terminates.intros)+
next
  case (Seq c\<^sub>1 c\<^sub>2)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c', s') \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'"
using Seq.prems by blast 
   have hyp': "(\<And>b c1. (redex (Seq c\<^sub>1 c\<^sub>2)  = Await b c1) \<Longrightarrow> \<Gamma>\<turnstile>c1 \<down> Normal s \<and> s\<in>b)" by fact 
  show ?case 
  proof (rule terminates.Seq)
    {
      fix c' s'
      assume step_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow> (c', s')"      
      assume red: "(\<And>b c1. (redex c\<^sub>1  = Await b c1) \<Longrightarrow> \<Gamma>\<turnstile>c1 \<down> Normal s \<and> s\<in>b)"
      have "\<Gamma>\<turnstile>c' \<down> s'"
      proof -
        from step_c\<^sub>1
        have "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (Seq c' c\<^sub>2, s')"
          by (simp add: step.Seq)          
        from hyp [OF this]
        have "\<Gamma>\<turnstile>Seq c' c\<^sub>2 \<down> s'".
        thus "\<Gamma>\<turnstile>c'\<down> s'"
          by cases auto
      qed
    } 
    from Seq.hyps (1) [OF this]
    show "\<Gamma>\<turnstile>c\<^sub>1 \<down> Normal s" using terminates_Skip' by (simp add: hyp') 
  next
    show "\<forall>s'. \<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> s' \<longrightarrow> \<Gamma>\<turnstile>c\<^sub>2 \<down> s'"
    proof (intro allI impI)
      fix s'
      assume exec_c\<^sub>1: "\<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> s'"
      show "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'"
      proof (cases "final (c\<^sub>1,Normal s)")
        case True
        hence "c\<^sub>1=Skip \<or> c\<^sub>1=Throw"
          by (simp add: final_def)
        thus ?thesis
        proof
          assume Skip: "c\<^sub>1=Skip"
          have s1:"\<Gamma>\<turnstile>(Seq Skip c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s) \<and>\<not> (\<exists>b c1. Seq c\<^sub>1 c\<^sub>2 = Await b c1)"
            by (simp add: step.SeqSkip)          
          from hyp 
          have "\<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s" using local.Skip s1 by blast 
          moreover from exec_c\<^sub>1 Skip
          have "s'=Normal s"
            by (auto elim: exec_Normal_elim_cases)
          ultimately show ?thesis by simp
        next
          assume Throw: "c\<^sub>1=Throw"
          with exec_c\<^sub>1 have "s'=Abrupt s"
            by (auto elim: exec_Normal_elim_cases)
          thus ?thesis
            by auto
        qed
      next
        case False        
        from exec_impl_steps [OF exec_c\<^sub>1]
        obtain c\<^sub>f t where 
          steps_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow>\<^sup>* (c\<^sub>f, t)" and
          fin:"(case s' of
                 Abrupt x \<Rightarrow> c\<^sub>f = Throw \<and> t = Normal x
                | _ \<Rightarrow> c\<^sub>f = Skip \<and> t = s')"
          by (fastforce split: xstate.splits)
        with fin have final: "final (c\<^sub>f,t)"
          by (cases s') (auto simp add: final_def)
        from split_computation [OF steps_c\<^sub>1 False this]
        obtain c'' s'' where
          first: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow> (c'', s'')" and
          rest: "\<Gamma>\<turnstile> (c'', s'') \<rightarrow>\<^sup>* (c\<^sub>f, t)" 
          by blast
        from step.Seq [OF first]
        have "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (Seq c'' c\<^sub>2, s'')" by auto
        from hyp [OF this]
        have termi_s'': "\<Gamma>\<turnstile>Seq c'' c\<^sub>2 \<down> s''".
        show ?thesis
        proof (cases s'')
          case (Normal x)
          from termi_s'' [simplified Normal]
          have termi_c\<^sub>2: "\<forall>t. \<Gamma>\<turnstile> \<langle>c'',Normal x\<rangle> \<Rightarrow> t \<longrightarrow> \<Gamma>\<turnstile>c\<^sub>2 \<down> t"
            by cases
          show ?thesis
          proof (cases "\<exists>x'. s'=Abrupt x'")
            case False
            with fin obtain "c\<^sub>f=Skip" "t=s'"
              by (cases s') auto
            from steps_Skip_impl_exec [OF rest [simplified this]] Normal
            have "\<Gamma>\<turnstile> \<langle>c'',Normal x\<rangle> \<Rightarrow> s'"
              by simp
            from termi_c\<^sub>2 [rule_format, OF this]
            show "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" .
          next
            case True
            with fin obtain x' where s': "s'=Abrupt x'" and "c\<^sub>f=Throw" "t=Normal x'"
              by auto
            from steps_Throw_impl_exec [OF rest [simplified this]] Normal 
            have "\<Gamma>\<turnstile> \<langle>c'',Normal x\<rangle> \<Rightarrow> Abrupt x'"
              by simp
            from termi_c\<^sub>2 [rule_format, OF this] s'
            show "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" by simp
           qed
        next
          case (Abrupt x)
          from steps_Abrupt_prop [OF rest this]
          have "t=Abrupt x" by simp
          with fin have "s'=Abrupt x"
            by (cases s') auto
          thus "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" 
            by auto
        next
          case (Fault f)
          from steps_Fault_prop [OF rest this]
          have "t=Fault f" by simp
          with fin have "s'=Fault f"
            by (cases s') auto
          thus "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" 
            by auto
        next
          case Stuck
          from steps_Stuck_prop [OF rest this]
          have "t=Stuck" by simp
          with fin have "s'=Stuck"
            by (cases s') auto
          thus "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" 
            by auto
        qed
      qed
    qed
  qed
next
  case (Cond b c\<^sub>1 c\<^sub>2)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Cond b c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c', s') \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'"
by (simp add: Cond.prems(1)) 
  show ?case
  proof (cases "s\<in>b") 
    case True
    then have "\<Gamma>\<turnstile> (Cond b c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c\<^sub>1, Normal s) "
     by (simp add: step.CondTrue)     
    from hyp [OF this] have "\<Gamma>\<turnstile>c\<^sub>1 \<down> Normal s".
    with True show ?thesis
      by (auto intro: terminates.intros)
  next
    case False
    then have "\<Gamma>\<turnstile> (Cond b c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c\<^sub>2, Normal s)"
      by (simp add: step.CondFalse)
    from hyp [OF this] have "\<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s".
    with False show ?thesis
      by (auto intro: terminates.intros)
  qed
next
  case (While b c)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (While b c, Normal s) \<rightarrow> (c', s')   \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  show ?case
  proof (cases "s\<in>b") 
    case True
    then have "\<Gamma>\<turnstile> (While b c, Normal s) \<rightarrow> (Seq c (While b c), Normal s)"
      by (simp add: step.WhileTrue)
    from hyp [OF this] have "\<Gamma>\<turnstile>(Seq c (While b c)) \<down> Normal s".
    with True show ?thesis
      by (auto elim: terminates_Normal_elim_cases intro: terminates.intros)
  next
    case False
    thus ?thesis
      by (auto intro: terminates.intros)
  qed
next
  case (Call p)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Call p, Normal s) \<rightarrow> (c', s')  \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by (simp add: Call.prems)
  show ?case
  proof (cases "\<Gamma> p")
    case None
    thus ?thesis
      by (auto intro: terminates.intros)
  next
    case (Some bdy)
    then have "\<Gamma>\<turnstile> (Call p, Normal s) \<rightarrow> (bdy, Normal s)"
      by (simp add: step.Call)
    from hyp [OF this] have "\<Gamma>\<turnstile>bdy \<down> Normal s".
    with Some show ?thesis
      by (auto intro: terminates.intros)
  qed
next
  case (DynCom c)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (DynCom c, Normal s) \<rightarrow> (c', s')  \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  have "\<Gamma>\<turnstile> (DynCom c, Normal s) \<rightarrow> (c s, Normal s)"
    by (simp add: step.DynCom)
  from hyp [OF this] have "\<Gamma>\<turnstile>c s \<down> Normal s".
  then show ?case
    by (auto intro: terminates.intros)
next
  case (Guard f g c)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Guard f g c, Normal s) \<rightarrow> (c', s')   \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  show ?case
  proof (cases "s\<in>g")
    case True
    then have "\<Gamma>\<turnstile> (Guard f g c, Normal s) \<rightarrow> (c, Normal s) "
      by (simp add: step.Guard) thm step.Guard
    from hyp [OF this] have "\<Gamma>\<turnstile>c\<down> Normal s".
    with True show ?thesis
      by (auto intro: terminates.intros)
  next
    case False
    thus ?thesis
      by (auto intro: terminates.intros)
  qed
next 
  case Throw show ?case by (auto intro: terminates.intros)
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c', s')   \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  have hyp': "(\<And>b c1. (redex (Catch c\<^sub>1 c\<^sub>2) = Await b c1) \<Longrightarrow> \<Gamma>\<turnstile>c1 \<down> Normal s \<and> s\<in>b)" by fact
  show ?case
  proof (rule terminates.Catch)
    {
      fix c' s'
      assume step_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow> (c', s')"
      assume red: "(\<And>b c1. (redex c\<^sub>1  = Await b c1) \<Longrightarrow> \<Gamma>\<turnstile>c1 \<down> Normal s \<and> s\<in>b)"
      have "\<Gamma>\<turnstile>c' \<down> s'"
      proof -
        from step_c\<^sub>1
        have "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (Catch c' c\<^sub>2, s') "
          by (simp add: step.Catch)
        from hyp [OF this]
        have "\<Gamma>\<turnstile>Catch c' c\<^sub>2 \<down> s'".
        thus "\<Gamma>\<turnstile>c'\<down> s'"
          by cases auto
      qed
    } 
    from Catch.hyps (1) [OF this]
    show "\<Gamma>\<turnstile>c\<^sub>1 \<down> Normal s" using terminates_Skip' by (simp add: hyp')
  next  
    show "\<forall>s'. \<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> Abrupt s' \<longrightarrow> \<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s'"
    proof (intro allI impI)
      fix s'
      assume exec_c\<^sub>1: "\<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> Abrupt s'"
      show "\<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s'"
      proof (cases "final (c\<^sub>1,Normal s)")
        case True
        with exec_c\<^sub>1
        have Throw: "c\<^sub>1=Throw"
          by (auto simp add: final_def elim: exec_Normal_elim_cases)
        have s1: "\<Gamma>\<turnstile>(Catch Throw c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s)"
          by (simp add: step.CatchThrow)
        from hyp 
        have "\<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s" using local.Throw s1 by blast 
        moreover from exec_c\<^sub>1 Throw
        have "s'=s"
          by (auto elim: exec_Normal_elim_cases)
        ultimately show ?thesis by simp
      next
        case False
        from exec_impl_steps [OF exec_c\<^sub>1]
        obtain c\<^sub>f t where 
          steps_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow>\<^sup>* (Throw, Normal s')" 
          by (fastforce split: xstate.splits)
        from split_computation [OF steps_c\<^sub>1 False]
        obtain c'' s'' where
          first: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow> (c'', s'')" and
          rest: "\<Gamma>\<turnstile> (c'', s'') \<rightarrow>\<^sup>* (Throw, Normal s')" 
          by (auto simp add: final_def)
        from step.Catch [OF first]
        have "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (Catch c'' c\<^sub>2, s'')" by auto
        from hyp [OF this] 
        have "\<Gamma>\<turnstile>Catch c'' c\<^sub>2 \<down> s''".
        moreover
        from steps_Throw_impl_exec [OF rest]
        have "\<Gamma>\<turnstile> \<langle>c'',s''\<rangle> \<Rightarrow> Abrupt s'".
        moreover
        from rest obtain x where "s''=Normal x"
          by (cases s'')
             (auto dest: steps_Fault_prop steps_Abrupt_prop steps_Stuck_prop)
        ultimately show ?thesis
          by (fastforce elim: terminates_elim_cases)
      qed
    qed
  qed
next
  case (Await b c) 
  have hyp':"\<And>ba c1. redex (Await b c) = Await ba c1 \<Longrightarrow> \<Gamma>\<turnstile>c1 \<down> Normal s \<and> s \<in> ba" by fact 
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Await b c, Normal s) \<rightarrow> (c', s') \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by (simp add: final_termi step_await_final1)
  have red:"redex (Await b c)  = Await b c" by auto  
  then have "\<And>b1 c1. (redex (Await b c)  = Await b1 c1) \<Longrightarrow> b1=b \<and> c1 = c" by simp
  then have " \<Gamma>\<turnstile>c \<down> Normal s \<and> s \<in> b" by (simp add: Await.prems(2))
  show ?case
  by (simp add: `\<Gamma>\<turnstile>c \<down> Normal s \<and> s \<in> b` terminates.AwaitTrue)      
qed


lemma wf_implies_termi_reach_step_case':
assumes hyp: "\<And>c' s'. \<Gamma>\<turnstile> (c, Normal s) \<rightarrow> (c', s')\<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" and
        hyp1:"~(\<exists>b c1. redex c = Await b c1)"
shows "\<Gamma>\<turnstile>c \<down> Normal s"
using hyp hyp1
proof (induct c)
  case Skip show ?case by (fastforce intro: terminates.intros)
next
  case Basic show ?case by (fastforce intro: terminates.intros)
next
  case (Spec r)
  show ?case
    by (cases "\<exists>t. (s,t)\<in>r") (fastforce intro: terminates.intros)+
next
  case (Seq c\<^sub>1 c\<^sub>2)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c', s') \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'"
using Seq.prems by blast
  have hyp': "~(\<exists>b c1. redex (Seq c\<^sub>1 c\<^sub>2) = Await b c1)" by fact
  show ?case 
  proof (rule terminates.Seq)
    {
      fix c' s'
      assume step_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow> (c', s')"
      assume red:  "~(\<exists>b c1. redex c\<^sub>1 = Await b c1)"      
      have "\<Gamma>\<turnstile>c' \<down> s'"
      proof -
        from step_c\<^sub>1
        have "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (Seq c' c\<^sub>2, s')"
          by (simp add: step.Seq)          
        from hyp [OF this]
        have "\<Gamma>\<turnstile>Seq c' c\<^sub>2 \<down> s'".
        thus "\<Gamma>\<turnstile>c'\<down> s'"
          by cases auto
      qed
    } 
    from Seq.hyps (1) [OF this]
    show "\<Gamma>\<turnstile>c\<^sub>1 \<down> Normal s"using hyp' by force 
  next
    show "\<forall>s'. \<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> s' \<longrightarrow> \<Gamma>\<turnstile>c\<^sub>2 \<down> s'"
    proof (intro allI impI)
      fix s'
      assume exec_c\<^sub>1: "\<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> s'"
      show "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'"
      proof (cases "final (c\<^sub>1,Normal s)")
        case True
        hence "c\<^sub>1=Skip \<or> c\<^sub>1=Throw"
          by (simp add: final_def)
        thus ?thesis
        proof
          assume Skip: "c\<^sub>1=Skip"
          have s1:"\<Gamma>\<turnstile>(Seq Skip c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s) \<and>\<not> (\<exists>b c1. Seq c\<^sub>1 c\<^sub>2 = Await b c1)"
            by (simp add: step.SeqSkip)          
          from hyp 
          have "\<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s" using local.Skip s1 by blast 
          moreover from exec_c\<^sub>1 Skip
          have "s'=Normal s"
            by (auto elim: exec_Normal_elim_cases)
          ultimately show ?thesis by simp
        next
          assume Throw: "c\<^sub>1=Throw"
          with exec_c\<^sub>1 have "s'=Abrupt s"
            by (auto elim: exec_Normal_elim_cases)
          thus ?thesis
            by auto
        qed
      next
        case False        
        from exec_impl_steps [OF exec_c\<^sub>1]
        obtain c\<^sub>f t where 
          steps_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow>\<^sup>* (c\<^sub>f, t)" and
          fin:"(case s' of
                 Abrupt x \<Rightarrow> c\<^sub>f = Throw \<and> t = Normal x
                | _ \<Rightarrow> c\<^sub>f = Skip \<and> t = s')"
          by (fastforce split: xstate.splits)
        with fin have final: "final (c\<^sub>f,t)"
          by (cases s') (auto simp add: final_def)
        from split_computation [OF steps_c\<^sub>1 False this]
        obtain c'' s'' where
          first: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow> (c'', s'')" and
          rest: "\<Gamma>\<turnstile> (c'', s'') \<rightarrow>\<^sup>* (c\<^sub>f, t)" 
          by blast
        from step.Seq [OF first]
        have "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (Seq c'' c\<^sub>2, s'')" by auto
        from hyp [OF this]
        have termi_s'': "\<Gamma>\<turnstile>Seq c'' c\<^sub>2 \<down> s''".
        show ?thesis
        proof (cases s'')
          case (Normal x)
          from termi_s'' [simplified Normal]
          have termi_c\<^sub>2: "\<forall>t. \<Gamma>\<turnstile> \<langle>c'',Normal x\<rangle> \<Rightarrow> t \<longrightarrow> \<Gamma>\<turnstile>c\<^sub>2 \<down> t"
            by cases
          show ?thesis
          proof (cases "\<exists>x'. s'=Abrupt x'")
            case False
            with fin obtain "c\<^sub>f=Skip" "t=s'"
              by (cases s') auto
            from steps_Skip_impl_exec [OF rest [simplified this]] Normal
            have "\<Gamma>\<turnstile> \<langle>c'',Normal x\<rangle> \<Rightarrow> s'"
              by simp
            from termi_c\<^sub>2 [rule_format, OF this]
            show "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" .
          next
            case True
            with fin obtain x' where s': "s'=Abrupt x'" and "c\<^sub>f=Throw" "t=Normal x'"
              by auto
            from steps_Throw_impl_exec [OF rest [simplified this]] Normal 
            have "\<Gamma>\<turnstile> \<langle>c'',Normal x\<rangle> \<Rightarrow> Abrupt x'"
              by simp
            from termi_c\<^sub>2 [rule_format, OF this] s'
            show "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" by simp
           qed
        next
          case (Abrupt x)
          from steps_Abrupt_prop [OF rest this]
          have "t=Abrupt x" by simp
          with fin have "s'=Abrupt x"
            by (cases s') auto
          thus "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" 
            by auto
        next
          case (Fault f)
          from steps_Fault_prop [OF rest this]
          have "t=Fault f" by simp
          with fin have "s'=Fault f"
            by (cases s') auto
          thus "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" 
            by auto
        next
          case Stuck
          from steps_Stuck_prop [OF rest this]
          have "t=Stuck" by simp
          with fin have "s'=Stuck"
            by (cases s') auto
          thus "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" 
            by auto
        qed
      qed
    qed
  qed
next
  case (Cond b c\<^sub>1 c\<^sub>2)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Cond b c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c', s') \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'"
by (simp add: Cond.prems(1)) 
  show ?case
  proof (cases "s\<in>b") 
    case True
    then have "\<Gamma>\<turnstile> (Cond b c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c\<^sub>1, Normal s) "
     by (simp add: step.CondTrue)     
    from hyp [OF this] have "\<Gamma>\<turnstile>c\<^sub>1 \<down> Normal s".
    with True show ?thesis
      by (auto intro: terminates.intros)
  next
    case False
    then have "\<Gamma>\<turnstile> (Cond b c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c\<^sub>2, Normal s)"
      by (simp add: step.CondFalse)
    from hyp [OF this] have "\<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s".
    with False show ?thesis
      by (auto intro: terminates.intros)
  qed
next
  case (While b c)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (While b c, Normal s) \<rightarrow> (c', s')   \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  show ?case
  proof (cases "s\<in>b") 
    case True
    then have "\<Gamma>\<turnstile> (While b c, Normal s) \<rightarrow> (Seq c (While b c), Normal s)"
      by (simp add: step.WhileTrue)
    from hyp [OF this] have "\<Gamma>\<turnstile>(Seq c (While b c)) \<down> Normal s".
    with True show ?thesis
      by (auto elim: terminates_Normal_elim_cases intro: terminates.intros)
  next
    case False
    thus ?thesis
      by (auto intro: terminates.intros)
  qed
next
  case (Call p)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Call p, Normal s) \<rightarrow> (c', s')  \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by (simp add: Call.prems)
  show ?case
  proof (cases "\<Gamma> p")
    case None
    thus ?thesis
      by (auto intro: terminates.intros)
  next
    case (Some bdy)
    then have "\<Gamma>\<turnstile> (Call p, Normal s) \<rightarrow> (bdy, Normal s)"
      by (simp add: step.Call)
    from hyp [OF this] have "\<Gamma>\<turnstile>bdy \<down> Normal s".
    with Some show ?thesis
      by (auto intro: terminates.intros)
  qed
next
  case (DynCom c)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (DynCom c, Normal s) \<rightarrow> (c', s')  \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  have "\<Gamma>\<turnstile> (DynCom c, Normal s) \<rightarrow> (c s, Normal s)"
    by (simp add: step.DynCom)
  from hyp [OF this] have "\<Gamma>\<turnstile>c s \<down> Normal s".
  then show ?case
    by (auto intro: terminates.intros)
next
  case (Guard f g c)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Guard f g c, Normal s) \<rightarrow> (c', s')   \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  show ?case
  proof (cases "s\<in>g")
    case True
    then have "\<Gamma>\<turnstile> (Guard f g c, Normal s) \<rightarrow> (c, Normal s) "
      by (simp add: step.Guard) thm step.Guard
    from hyp [OF this] have "\<Gamma>\<turnstile>c\<down> Normal s".
    with True show ?thesis
      by (auto intro: terminates.intros)
  next
    case False
    thus ?thesis
      by (auto intro: terminates.intros)
  qed
next 
  case Throw show ?case by (auto intro: terminates.intros)
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c', s')   \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  have hyp': "~(\<exists>b c1. redex (Catch c\<^sub>1 c\<^sub>2) = Await b c1)" by fact
  show ?case
  proof (rule terminates.Catch)
    {
      fix c' s'
      assume step_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow> (c', s')"
      assume red: "~(\<exists>b c1. redex c\<^sub>1  = Await b c1)"
      have "\<Gamma>\<turnstile>c' \<down> s'"
      proof -
        from step_c\<^sub>1
        have "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (Catch c' c\<^sub>2, s') "
          by (simp add: step.Catch)
        from hyp [OF this]
        have "\<Gamma>\<turnstile>Catch c' c\<^sub>2 \<down> s'".
        thus "\<Gamma>\<turnstile>c'\<down> s'"
          by cases auto
      qed
    } 
    from Catch.hyps (1) [OF this]
    show "\<Gamma>\<turnstile>c\<^sub>1 \<down> Normal s" using hyp' by force
  next  
    show "\<forall>s'. \<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> Abrupt s' \<longrightarrow> \<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s'"
    proof (intro allI impI)
      fix s'
      assume exec_c\<^sub>1: "\<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> Abrupt s'"
      show "\<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s'"
      proof (cases "final (c\<^sub>1,Normal s)")
        case True
        with exec_c\<^sub>1
        have Throw: "c\<^sub>1=Throw"
          by (auto simp add: final_def elim: exec_Normal_elim_cases)
        have s1: "\<Gamma>\<turnstile>(Catch Throw c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s)"
          by (simp add: step.CatchThrow)
        from hyp 
        have "\<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s" using local.Throw s1 by blast 
        moreover from exec_c\<^sub>1 Throw
        have "s'=s"
          by (auto elim: exec_Normal_elim_cases)
        ultimately show ?thesis by simp
      next
        case False
        from exec_impl_steps [OF exec_c\<^sub>1]
        obtain c\<^sub>f t where 
          steps_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow>\<^sup>* (Throw, Normal s')" 
          by (fastforce split: xstate.splits)
        from split_computation [OF steps_c\<^sub>1 False]
        obtain c'' s'' where
          first: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow> (c'', s'')" and
          rest: "\<Gamma>\<turnstile> (c'', s'') \<rightarrow>\<^sup>* (Throw, Normal s')" 
          by (auto simp add: final_def)
        from step.Catch [OF first]
        have "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (Catch c'' c\<^sub>2, s'')" by auto
        from hyp [OF this] 
        have "\<Gamma>\<turnstile>Catch c'' c\<^sub>2 \<down> s''".
        moreover
        from steps_Throw_impl_exec [OF rest]
        have "\<Gamma>\<turnstile> \<langle>c'',s''\<rangle> \<Rightarrow> Abrupt s'".
        moreover
        from rest obtain x where "s''=Normal x"
          by (cases s'')
             (auto dest: steps_Fault_prop steps_Abrupt_prop steps_Stuck_prop)
        ultimately show ?thesis
          by (fastforce elim: terminates_elim_cases)
      qed
    qed
  qed
next
  case (Await b c)       
  show ?case
  using Await.prems(2) by auto   
qed


lemma Await_finish:"\<And>c2 s2 b c. \<Gamma>\<turnstile> (Await b c, s1) \<rightarrow> (c2, s2) \<Longrightarrow> \<Gamma>\<turnstile>c2 \<down> s2"
by (metis Abrupt Fault Stuck final_termi step_await_final1 step_preserves_termination xstate.exhaust)

                                                            
lemma wf_implies_termi_reach:
assumes wf: "wf {(cfg2,cfg1). \<Gamma> \<turnstile> (c,s) \<rightarrow>\<^sup>* cfg1 \<and> \<Gamma> \<turnstile> cfg1 \<rightarrow> cfg2}"
shows "\<And>c1 s1. \<lbrakk>\<Gamma> \<turnstile> (c,s) \<rightarrow>\<^sup>* cfg1;  cfg1=(c1,s1)\<rbrakk>\<Longrightarrow> \<Gamma>\<turnstile>c1\<down>s1"
using wf 
proof (induct cfg1,simp)
  fix c1 s1
  assume reach: "\<Gamma>\<turnstile> (c, s) \<rightarrow>\<^sup>* (c1, s1)"
  assume hyp_raw: "\<And>y c2 s2.
           \<lbrakk>\<Gamma>\<turnstile> (c1, s1) \<rightarrow> (c2, s2); \<Gamma>\<turnstile> (c, s) \<rightarrow>\<^sup>* (c2, s2); y = (c2, s2)\<rbrakk>
           \<Longrightarrow> \<Gamma>\<turnstile>c2 \<down> s2"
  have hyp: "\<And>c2 s2. \<Gamma>\<turnstile> (c1, s1) \<rightarrow> (c2, s2) \<Longrightarrow> \<Gamma>\<turnstile>c2 \<down> s2"
    apply -
    apply (rule hyp_raw)
    apply   assumption
    using reach 
    apply  simp
    apply (rule refl)
    done
  
  show "\<Gamma>\<turnstile>c1 \<down> s1"
  proof (cases s1)  
    case (Normal s1')             
    with  wf_implies_termi_reach_step_case' [OF hyp [simplified Normal]] 
    show ?thesis
      by auto
  qed (auto intro: terminates.intros)
qed

theorem no_infinite_computation_impl_terminates:
  assumes not_inf: "\<not> \<Gamma>\<turnstile> (c, s) \<rightarrow> \<dots>(\<infinity>)"
  shows "\<Gamma>\<turnstile>c\<down>s"
proof -
  from no_infinite_computation_implies_wf [OF not_inf]
  have wf: "wf {(c2, c1). \<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* c1 \<and> \<Gamma>\<turnstile>c1 \<rightarrow> c2}".
  show ?thesis
    by (rule wf_implies_termi_reach [OF wf]) auto
qed

corollary terminates_iff_no_infinite_computation: 
  "\<Gamma>\<turnstile>c\<down>s = (\<not> \<Gamma>\<turnstile> (c, s) \<rightarrow> \<dots>(\<infinity>))"
  apply (rule)
  apply  (erule terminates_impl_no_infinite_computation)
  apply (erule no_infinite_computation_impl_terminates)
  done

(* ************************************************************************* *)
subsection {* Generalised Redexes *} 
(* ************************************************************************* *)

text {*
For an important lemma for the completeness proof of the Hoare-logic for
total correctness we need a generalisation of @{const "redex"} that not only
yield the redex itself but all the enclosing statements as well.
*}

primrec redexes:: "('s,'p,'f,'e)com \<Rightarrow> ('s,'p,'f,'e)com set"
where
"redexes Skip = {Skip}" |
"redexes (Basic f) = {Basic f}" |
"redexes (Spec r) = {Spec r}" |
"redexes (Seq c\<^sub>1 c\<^sub>2) = {Seq c\<^sub>1 c\<^sub>2} \<union> redexes c\<^sub>1" |
"redexes (Cond b c\<^sub>1 c\<^sub>2) = {Cond b c\<^sub>1 c\<^sub>2}" |
"redexes (While b c) = {While b c}" |
"redexes (Call p) = {Call p}" |
"redexes (DynCom d) = {DynCom d}" |
"redexes (Guard f b c) = {Guard f b c}" |
"redexes (Throw) = {Throw}" |
"redexes (Catch c\<^sub>1 c\<^sub>2) = {Catch c\<^sub>1 c\<^sub>2} \<union> redexes c\<^sub>1" |
"redexes (Await b c) = {Await b c}"

lemma root_in_redexes: "c \<in> redexes c"
  apply (induct c)
  apply auto
  done

lemma redex_in_redexes: "redex c \<in> redexes c"
  apply (induct c)
  apply auto
  done

lemma redex_redexes: "\<And>c'. \<lbrakk>c' \<in> redexes c; redex c' = c'\<rbrakk> \<Longrightarrow> redex c = c'" 
  apply (induct c)
  apply auto
  done

lemma step_redexes:
  shows "\<And>r r'. \<lbrakk>\<Gamma>\<turnstile>(r,s) \<rightarrow> (r',s'); r \<in> redexes c\<rbrakk> 
  \<Longrightarrow> \<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow> (c',s') \<and> r' \<in> redexes c'"
proof (induct c)
  case Skip thus ?case by (fastforce intro: step.intros elim: step_elim_cases)
next
  case Basic thus ?case by (fastforce intro: step.intros elim: step_elim_cases)
next
  case Spec thus ?case by (fastforce intro: step.intros elim: step_elim_cases)
next
  case (Seq c\<^sub>1 c\<^sub>2)
  have "r \<in> redexes (Seq c\<^sub>1 c\<^sub>2)" by fact
  hence r: "r = Seq c\<^sub>1 c\<^sub>2 \<or> r \<in> redexes c\<^sub>1"
    by simp
  have step_r: "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r', s')" by fact
  from r show ?case
  proof 
    assume "r = Seq c\<^sub>1 c\<^sub>2"
    with step_r
    show ?case
      by (auto simp add: root_in_redexes)
  next
    assume r: "r \<in> redexes c\<^sub>1"
    from Seq.hyps (1) [OF step_r this] 
    obtain c' where 
      step_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, s) \<rightarrow> (c', s')" and
      r': "r' \<in> redexes c'"
      by blast
    from step.Seq [OF step_c\<^sub>1]
    have "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, s) \<rightarrow> (Seq c' c\<^sub>2, s')".
    with r'
    show ?case
      by auto
  qed
next
  case Cond 
  thus ?case 
    by (fastforce intro: step.intros elim: step_elim_cases simp add: root_in_redexes)
next
  case While 
  thus ?case 
    by (fastforce intro: step.intros elim: step_elim_cases simp add: root_in_redexes)
next
  case Call thus ?case 
    by (fastforce intro: step.intros elim: step_elim_cases simp add: root_in_redexes)
next
  case DynCom thus ?case 
    by (fastforce intro: step.intros elim: step_elim_cases simp add: root_in_redexes)
next
  case Guard thus ?case 
    by (fastforce intro: step.intros elim: step_elim_cases simp add: root_in_redexes)
next
  case Throw thus ?case 
    by (fastforce intro: step.intros elim: step_elim_cases simp add: root_in_redexes)
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have "r \<in> redexes (Catch c\<^sub>1 c\<^sub>2)" by fact
  hence r: "r = Catch c\<^sub>1 c\<^sub>2 \<or> r \<in> redexes c\<^sub>1"
    by simp
  have step_r: "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r', s')" by fact
  from r show ?case
  proof 
    assume "r = Catch c\<^sub>1 c\<^sub>2"
    with step_r
    show ?case
      by (auto simp add: root_in_redexes)
  next
    assume r: "r \<in> redexes c\<^sub>1"
    from Catch.hyps (1) [OF step_r this] 
    obtain c' where 
      step_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, s) \<rightarrow> (c', s')" and
      r': "r' \<in> redexes c'"
      by blast
    from step.Catch [OF step_c\<^sub>1]
    have "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, s) \<rightarrow> (Catch c' c\<^sub>2, s')".
    with r'
    show ?case
      by auto
  qed
next case (Await b c)  
     thus ?case 
     by (fastforce intro: step.intros elim: step_elim_cases simp add: root_in_redexes)
qed 

lemma steps_redexes:
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>* (r', s')"
  shows "\<And>c. r \<in> redexes c \<Longrightarrow> \<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* (c',s') \<and> r' \<in> redexes c'"
using steps 
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl
  then
  show "\<exists>c'. \<Gamma>\<turnstile> (c, s') \<rightarrow>\<^sup>* (c', s') \<and> r' \<in> redexes c'"
    by auto
next
  case (Trans r s r'' s'')
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r'', s'')" "r \<in> redexes c" by fact+
  from step_redexes [OF this]
  obtain c' where
    step: "\<Gamma>\<turnstile> (c, s) \<rightarrow> (c', s'')" and
    r'': "r'' \<in> redexes c'"
    by blast
  note step
  also
  from Trans.hyps (3) [OF r'']
  obtain c'' where
    steps: "\<Gamma>\<turnstile> (c', s'') \<rightarrow>\<^sup>* (c'', s')" and
    r': "r' \<in> redexes c''"
    by blast
  note steps
  finally
  show ?case
    using r'
    by blast
qed



lemma steps_redexes':
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>+ (r', s')"
  shows "\<And>c. r \<in> redexes c \<Longrightarrow> \<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>+ (c',s') \<and> r' \<in> redexes c'"
using steps 
proof (induct rule: tranclp_induct2 [consumes 1, case_names Step Trans])
  case (Step r' s' c') 
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r', s')" "r \<in> redexes c'" by fact+
  from step_redexes [OF this]
  show ?case
    by (blast intro: r_into_trancl)
next
  case (Trans r' s' r'' s'')
  from Trans obtain c' where
    steps: "\<Gamma>\<turnstile> (c, s) \<rightarrow>\<^sup>+ (c', s')" and
    r': "r' \<in> redexes c'"
    by blast
  note steps
  moreover
  have "\<Gamma>\<turnstile> (r', s') \<rightarrow> (r'', s'')" by fact
  from step_redexes [OF this r'] obtain c'' where
    step: "\<Gamma>\<turnstile> (c', s') \<rightarrow> (c'', s'')" and
    r'': "r'' \<in> redexes c''"
    by blast
  note step
  finally show ?case
    using r'' by blast
qed

lemma step_redexes_Seq:
  assumes step: "\<Gamma>\<turnstile>(r,s) \<rightarrow> (r',s')"
  assumes Seq: "Seq r c\<^sub>2 \<in> redexes c"
  shows "\<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow> (c',s') \<and> Seq r' c\<^sub>2 \<in> redexes c'"
proof -
  from step.Seq [OF step]
  have "\<Gamma>\<turnstile> (Seq r c\<^sub>2, s) \<rightarrow> (Seq r' c\<^sub>2, s')".
  from step_redexes [OF this Seq] 
  show ?thesis .
qed

lemma steps_redexes_Seq:
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>* (r', s')"
  shows "\<And>c. Seq r c\<^sub>2 \<in> redexes c \<Longrightarrow> 
              \<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* (c',s') \<and> Seq r' c\<^sub>2 \<in> redexes c'"
using steps 
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl
  then show ?case
    by (auto)

next
  case (Trans r s r'' s'')
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r'', s'')" "Seq r c\<^sub>2 \<in> redexes c" by fact+
  from step_redexes_Seq [OF this]
  obtain c' where
    step: "\<Gamma>\<turnstile> (c, s) \<rightarrow> (c', s'')" and
    r'': "Seq r'' c\<^sub>2 \<in> redexes c'"
    by blast
  note step
  also
  from Trans.hyps (3) [OF r'']
  obtain c'' where
    steps: "\<Gamma>\<turnstile> (c', s'') \<rightarrow>\<^sup>* (c'', s')" and
    r': "Seq r' c\<^sub>2 \<in> redexes c''"
    by blast
  note steps
  finally
  show ?case
    using r'
    by blast
qed

lemma steps_redexes_Seq':
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>+ (r', s')"
  shows "\<And>c. Seq r c\<^sub>2 \<in> redexes c 
             \<Longrightarrow> \<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>+ (c',s') \<and> Seq r' c\<^sub>2 \<in> redexes c'"
using steps 
proof (induct rule: tranclp_induct2 [consumes 1, case_names Step Trans])
  case (Step r' s' c') 
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r', s')" "Seq r c\<^sub>2 \<in> redexes c'" by fact+
  from step_redexes_Seq [OF this]
  show ?case
    by (blast intro: r_into_trancl)
next
  case (Trans r' s' r'' s'')
  from Trans obtain c' where
    steps: "\<Gamma>\<turnstile> (c, s) \<rightarrow>\<^sup>+ (c', s')" and
    r': "Seq r' c\<^sub>2 \<in> redexes c'"
    by blast
  note steps
  moreover
  have "\<Gamma>\<turnstile> (r', s') \<rightarrow> (r'', s'')" by fact
  from step_redexes_Seq [OF this r'] obtain c'' where
    step: "\<Gamma>\<turnstile> (c', s') \<rightarrow> (c'', s'')" and
    r'': "Seq r'' c\<^sub>2 \<in> redexes c''"
    by blast
  note step
  finally show ?case
    using r'' by blast
qed

lemma step_redexes_Catch:
  assumes step: "\<Gamma>\<turnstile>(r,s) \<rightarrow> (r',s')"
  assumes Catch: "Catch r c\<^sub>2 \<in> redexes c"
  shows "\<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow> (c',s') \<and> Catch r' c\<^sub>2 \<in> redexes c'"
proof -
  from step.Catch [OF step]
  have "\<Gamma>\<turnstile> (Catch r c\<^sub>2, s) \<rightarrow> (Catch r' c\<^sub>2, s')".
  from step_redexes [OF this Catch] 
  show ?thesis .
qed

lemma steps_redexes_Catch:
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>* (r', s')"
  shows "\<And>c. Catch r c\<^sub>2 \<in> redexes c \<Longrightarrow> 
              \<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* (c',s') \<and> Catch r' c\<^sub>2 \<in> redexes c'"
using steps 
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl
  then show ?case
    by (auto)

next
  case (Trans r s r'' s'')
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r'', s'')" "Catch r c\<^sub>2 \<in> redexes c" by fact+
  from step_redexes_Catch [OF this]
  obtain c' where
    step: "\<Gamma>\<turnstile> (c, s) \<rightarrow> (c', s'')" and
    r'': "Catch r'' c\<^sub>2 \<in> redexes c'"
    by blast
  note step
  also
  from Trans.hyps (3) [OF r'']
  obtain c'' where
    steps: "\<Gamma>\<turnstile> (c', s'') \<rightarrow>\<^sup>* (c'', s')" and
    r': "Catch r' c\<^sub>2 \<in> redexes c''"
    by blast
  note steps
  finally
  show ?case
    using r'
    by blast
qed

lemma steps_redexes_Catch':
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>+ (r', s')"
  shows "\<And>c. Catch r c\<^sub>2 \<in> redexes c 
             \<Longrightarrow> \<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>+ (c',s') \<and> Catch r' c\<^sub>2 \<in> redexes c'"
using steps 
proof (induct rule: tranclp_induct2 [consumes 1, case_names Step Trans])
  case (Step r' s' c') 
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r', s')" "Catch r c\<^sub>2 \<in> redexes c'" by fact+
  from step_redexes_Catch [OF this]
  show ?case
    by (blast intro: r_into_trancl)
next
  case (Trans r' s' r'' s'')
  from Trans obtain c' where
    steps: "\<Gamma>\<turnstile> (c, s) \<rightarrow>\<^sup>+ (c', s')" and
    r': "Catch r' c\<^sub>2 \<in> redexes c'"
    by blast
  note steps
  moreover
  have "\<Gamma>\<turnstile> (r', s') \<rightarrow> (r'', s'')" by fact
  from step_redexes_Catch [OF this r'] obtain c'' where
    step: "\<Gamma>\<turnstile> (c', s') \<rightarrow> (c'', s'')" and
    r'': "Catch r'' c\<^sub>2 \<in> redexes c''"
    by blast
  note step
  finally show ?case
    using r'' by blast
qed

lemma redexes_subset:"\<And>c'. c' \<in> redexes c \<Longrightarrow> redexes c' \<subseteq> redexes c"
  by (induct c) auto

lemma redexes_preserves_termination:
  assumes termi: "\<Gamma>\<turnstile>c\<down>s"
  shows "\<And>c'. c' \<in> redexes c \<Longrightarrow> \<Gamma>\<turnstile>c'\<down>s"  
using termi
by induct (auto intro: terminates.intros)

*)
end
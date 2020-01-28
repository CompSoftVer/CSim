(*
    Author:      David Sanan
    Maintainer:  David Sanan, sanan at ntu edu sg
    License:     LGPL
*)

(*  Title:      SemanticCon.thy
    Author:     Norbert Schirmer, TU Muenchen
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

section {* Big-Step Semantics for Simpl *}
theory SemanticCon imports LanguageCon "EmbSimpl.Semantic" begin

notation
restrict_map  ("_|\<^bsub>_\<^esub>" [90, 91] 90)


definition isAbr::"('s,'f) xstate \<Rightarrow> bool"
  where "isAbr S = (\<exists>s. S=Abrupt s)"
 
lemma isAbr_simps [simp]:
"isAbr (Normal s) = False"
"isAbr (Abrupt s) = True"
"isAbr (Fault f) = False"
"isAbr Stuck = False"
by (auto simp add: isAbr_def)

lemma isAbrE [consumes 1, elim?]: "\<lbrakk>isAbr S; \<And>s. S=Abrupt s \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp add: isAbr_def)

lemma not_isAbrD: 
"\<not> isAbr s \<Longrightarrow> (\<exists>s'. s=Normal s') \<or> s = Stuck \<or> (\<exists>f. s=Fault f)"
  by (cases s) auto

definition isFault:: "('s,'f) xstate \<Rightarrow> bool"
  where "isFault S = (\<exists>f. S=Fault f)"

lemma isFault_simps [simp]:
"isFault (Normal s) = False"
"isFault (Abrupt s) = False"
"isFault (Fault f) = True"
"isFault Stuck = False"
by (auto simp add: isFault_def)

lemma isFaultE [consumes 1, elim?]: "\<lbrakk>isFault s; \<And>f. s=Fault f \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp add: isFault_def)

lemma not_isFault_iff: "(\<not> isFault t) = (\<forall>f. t \<noteq> Fault f)"
  by (auto elim: isFaultE)

(* ************************************************************************* *)
subsection {* Big-Step Execution: @{text "\<Gamma>\<turnstile>\<langle>c, s\<rangle> \<Rightarrow> t"} *}
(* ************************************************************************* *)

text {* The procedure environment *}
type_synonym ('s,'p,'f,'e) body = "'p \<Rightarrow> ('s,'p,'f,'e) com option"

definition no_await_body :: "('s,'p,'f,'e) body \<Rightarrow> ('s,'p,'f) Semantic.body" ("_\<^sub>\<not>\<^sub>a" [98])
where
"no_await_body \<Gamma> \<equiv> (\<lambda>x. case (\<Gamma> x) of (Some t) \<Rightarrow> if (noawaits t) then Some (sequential t) else None
                         | None \<Rightarrow> None
                    )
"

definition parallel_env::"('s,'p,'f) Semantic.body \<Rightarrow>('s,'p,'f,'e') body "
  where
"parallel_env \<Gamma> = (\<lambda>x. case (\<Gamma> x) of (Some t) \<Rightarrow> Some (parallel t)
                                      | None \<Rightarrow> None)"



lemma in_gamma_in_noawait_gamma:
    "\<forall>p. p\<in>dom (\<Gamma>\<^sub>\<not>\<^sub>a) \<longrightarrow> p\<in> dom \<Gamma>"
 by (simp add: domIff no_await_body_def option.case_eq_if) 


lemma no_await_some_some_p: 
     assumes not_none:"\<Gamma>\<^sub>\<not>\<^sub>a p = Some s"
     shows "(\<Gamma> p) = None \<Longrightarrow> P"
proof -
  assume "\<Gamma> p = None"
  hence "None = \<Gamma>\<^sub>\<not>\<^sub>a p"
    by (simp add: no_await_body_def)
  thus ?thesis
    by (simp add: not_none)
qed


lemma no_await_some_no_await: 
     assumes not_none:"\<Gamma>\<^sub>\<not>\<^sub>a p = Some s \<and> (\<Gamma> p) = Some t"
     shows "noawaits t"
proof -
  have "None \<noteq> \<Gamma>\<^sub>\<not>\<^sub>a p"
    using not_none by auto
  hence "(if noawaits t then Some (sequential t) else None) \<noteq> None"
    by (simp add: no_await_body_def not_none)
  thus ?thesis
    by meson
qed

lemma lam1_seq:"\<Gamma>1=\<Gamma>\<^sub>\<not>\<^sub>a \<Longrightarrow> \<Gamma>1 p = Some s \<Longrightarrow> \<Gamma> p = Some t \<Longrightarrow> s=sequential t"
unfolding no_await_body_def
proof -
  assume a1: "\<Gamma>1 p = Some s"
  assume a2: "\<Gamma>1 = (\<lambda>x. case \<Gamma> x of None \<Rightarrow> None | Some t \<Rightarrow> if noawaits t then Some (sequential t) else None)"
  assume "\<Gamma> p = Some t"
  hence "(if noawaits t then Some (sequential t) else None) = \<Gamma>1 p"
    using a2 by force
  thus ?thesis
    using a1 by (metis (no_types) option.distinct(2) option.inject)
qed


inductive 
  "exec"::"[('s,'p,'f,'e) body,('s,'p,'f,'e) com,('s,'f) xstate,('s,'f) xstate] 
                    \<Rightarrow> bool" ("_\<turnstile>\<^sub>p \<langle>_,_\<rangle> \<Rightarrow> _"  [60,20,98,98] 89)
  for \<Gamma>::"('s,'p,'f,'e) body"
where
  Skip: "\<Gamma>\<turnstile>\<^sub>p\<langle>Skip,Normal s\<rangle> \<Rightarrow> Normal s"
 
| Guard: "\<lbrakk>s\<in>g; \<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> \<Rightarrow>  t\<rbrakk> 
          \<Longrightarrow> 
          \<Gamma>\<turnstile>\<^sub>p\<langle>Guard f g c,Normal s\<rangle> \<Rightarrow>  t"

| GuardFault: "s\<notin>g \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>Guard f g c,Normal s\<rangle> \<Rightarrow>  Fault f"

| FaultProp [intro,simp]: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Fault f\<rangle> \<Rightarrow>  Fault f" 

| Basic: "\<Gamma>\<turnstile>\<^sub>p\<langle>Basic f e,Normal s\<rangle> \<Rightarrow>  Normal (f s)"

| Spec: "(s,t) \<in> r 
         \<Longrightarrow> 
         \<Gamma>\<turnstile>\<^sub>p\<langle>Spec r e,Normal s\<rangle> \<Rightarrow>  Normal t"

| SpecStuck: "\<forall>t. (s,t) \<notin> r 
              \<Longrightarrow> 
              \<Gamma>\<turnstile>\<^sub>p\<langle>Spec r e,Normal s\<rangle> \<Rightarrow>  Stuck"

| Seq: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow>  s'; \<Gamma>\<turnstile>\<^sub>p\<langle>c\<^sub>2,s'\<rangle> \<Rightarrow>  t\<rbrakk>
        \<Longrightarrow>
        \<Gamma>\<turnstile>\<^sub>p\<langle>Seq c\<^sub>1 c\<^sub>2,Normal s\<rangle> \<Rightarrow>  t" 

| CondTrue: "\<lbrakk>s \<in> b; \<Gamma>\<turnstile>\<^sub>p\<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow>  t\<rbrakk> 
             \<Longrightarrow>  
             \<Gamma>\<turnstile>\<^sub>p\<langle>Cond b c\<^sub>1 c\<^sub>2,Normal s\<rangle> \<Rightarrow>  t"

| CondFalse: "\<lbrakk>s \<notin> b; \<Gamma>\<turnstile>\<^sub>p\<langle>c\<^sub>2,Normal s\<rangle> \<Rightarrow>  t\<rbrakk> 
              \<Longrightarrow>  
              \<Gamma>\<turnstile>\<^sub>p\<langle>Cond b c\<^sub>1 c\<^sub>2,Normal s\<rangle> \<Rightarrow>  t"

| WhileTrue: "\<lbrakk>s \<in> b; \<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> \<Rightarrow>  s'; \<Gamma>\<turnstile>\<^sub>p\<langle>While b c,s'\<rangle> \<Rightarrow>  t\<rbrakk> 
              \<Longrightarrow>  
              \<Gamma>\<turnstile>\<^sub>p\<langle>While b c,Normal s\<rangle> \<Rightarrow>  t"
  
| AwaitTrue: "\<lbrakk>s \<in> b; \<Gamma>\<^sub>p=\<Gamma>\<^sub>\<not>\<^sub>a ; \<Gamma>\<^sub>p\<turnstile>\<langle>ca,Normal s\<rangle> \<Rightarrow>  t\<rbrakk> 
              \<Longrightarrow>  
              \<Gamma>\<turnstile>\<^sub>p\<langle>Await b ca e,Normal s\<rangle> \<Rightarrow>  t"

| AwaitFalse: "\<lbrakk>s \<notin> b\<rbrakk> 
              \<Longrightarrow>  
              \<Gamma>\<turnstile>\<^sub>p\<langle>Await b ca e,Normal s\<rangle> \<Rightarrow>  Normal s"

| WhileFalse: "\<lbrakk>s \<notin> b\<rbrakk> 
               \<Longrightarrow>  
               \<Gamma>\<turnstile>\<^sub>p\<langle>While b c,Normal s\<rangle> \<Rightarrow>  Normal s"

| Call:  "\<lbrakk>\<Gamma> p=Some bdy;\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal s\<rangle> \<Rightarrow>  t\<rbrakk> 
          \<Longrightarrow> 
          \<Gamma>\<turnstile>\<^sub>p\<langle>Call p,Normal s\<rangle> \<Rightarrow>  t"
  
| CallUndefined: "\<lbrakk>\<Gamma> p=None\<rbrakk> 
                  \<Longrightarrow> 
                  \<Gamma>\<turnstile>\<^sub>p\<langle>Call p,Normal s\<rangle> \<Rightarrow>  Stuck"

| StuckProp [intro,simp]: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Stuck\<rangle> \<Rightarrow>  Stuck"

| DynCom:  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>(c s),Normal s\<rangle> \<Rightarrow>  t\<rbrakk> 
             \<Longrightarrow> 
             \<Gamma>\<turnstile>\<^sub>p\<langle>DynCom c,Normal s\<rangle> \<Rightarrow>  t"

| Throw: "\<Gamma>\<turnstile>\<^sub>p\<langle>Throw,Normal s\<rangle> \<Rightarrow>  Abrupt s"

| AbruptProp [intro,simp]: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Abrupt s\<rangle> \<Rightarrow>  Abrupt s"
  
| CatchMatch: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow>  Abrupt s'; \<Gamma>\<turnstile>\<^sub>p\<langle>c\<^sub>2,Normal s'\<rangle> \<Rightarrow>  t\<rbrakk>
               \<Longrightarrow>
               \<Gamma>\<turnstile>\<^sub>p\<langle>Catch c\<^sub>1 c\<^sub>2,Normal s\<rangle> \<Rightarrow>  t" 
| CatchMiss: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow>  t; \<not>isAbr t\<rbrakk>
               \<Longrightarrow>
               \<Gamma>\<turnstile>\<^sub>p\<langle>Catch c\<^sub>1 c\<^sub>2,Normal s\<rangle> \<Rightarrow>  t" 

inductive_cases exec_elim_cases [cases set]:
  "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Fault f\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Stuck\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Abrupt s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Skip,s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Seq c1 c2,s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Guard f g c,s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Basic f e,s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Spec r e,s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Cond b c1 c2,s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Await b c e,s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Call p,s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>DynCom c,s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Throw,s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Catch c1 c2,s\<rangle> \<Rightarrow>  t"

inductive_cases exec_Normal_elim_cases [cases set]: 
  "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Fault f\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Stuck\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Abrupt s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Skip,Normal s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Guard f g c,Normal s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Basic f e,Normal s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Spec r e,Normal s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Seq c1 c2,Normal s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Cond b c1 c2,Normal s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,Normal s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Await b c e,Normal s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Call p,Normal s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>DynCom c,Normal s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Throw,Normal s\<rangle> \<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Catch c1 c2,Normal s\<rangle> \<Rightarrow>  t"

text{*Relation between Concurrent Semantics and Sequential semantics*}

lemma exec_seq_parallel: 
  assumes a0:"\<Gamma>\<turnstile>\<langle>bdy,s\<rangle> \<Rightarrow>  t"
  shows "(parallel_env \<Gamma>)\<turnstile>\<^sub>p \<langle>parallel bdy,s\<rangle> \<Rightarrow>  t"
  using a0
proof(induct) 
case (Call p bdy s t)
  then show ?case by (simp add: SemanticCon.exec.Call parallel_env_def) 
next
  case (CallUndefined p s)
  then show ?case
    by (simp add: SemanticCon.exec.CallUndefined parallel_env_def)
next
  case (CatchMiss c\<^sub>1 s t c\<^sub>2)
  then show ?case
    using Semantic.isAbr_def SemanticCon.exec.CatchMiss SemanticCon.isAbrE by fastforce 
qed(fastforce intro: exec.intros)+


lemma exec_block: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow>  Normal t; \<Gamma>\<turnstile>\<^sub>p\<langle>c s t,Normal (return s t)\<rangle> \<Rightarrow>  u\<rbrakk>
  \<Longrightarrow> 
  \<Gamma>\<turnstile>\<^sub>p\<langle>block init ei bdy return er c,Normal s\<rangle> \<Rightarrow>  u"
apply (unfold block_def)
by (fastforce intro: exec.intros)

lemma exec_blockAbrupt: 
     "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow>  Abrupt t\<rbrakk>
       \<Longrightarrow> 
       \<Gamma>\<turnstile>\<^sub>p\<langle>block init ei bdy return er c,Normal s\<rangle> \<Rightarrow>  Abrupt (return s t)"
apply (unfold block_def)
by (fastforce intro: exec.intros)

lemma exec_blockFault: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow>  Fault f\<rbrakk>
   \<Longrightarrow> 
  \<Gamma>\<turnstile>\<^sub>p\<langle>block init ei bdy return er c,Normal s\<rangle> \<Rightarrow>  Fault f"
apply (unfold block_def)
by (fastforce intro: exec.intros)

lemma exec_blockStuck:
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow>  Stuck\<rbrakk>
  \<Longrightarrow> 
  \<Gamma>\<turnstile>\<^sub>p\<langle>block init ei bdy return er c,Normal s\<rangle> \<Rightarrow>  Stuck"
apply (unfold block_def)
by (fastforce intro: exec.intros)

lemma exec_call:   
 "\<lbrakk>\<Gamma> p=Some bdy;\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow>  Normal t; \<Gamma>\<turnstile>\<^sub>p\<langle>c s t,Normal (return s t)\<rangle> \<Rightarrow>  u\<rbrakk> 
  \<Longrightarrow> 
  \<Gamma>\<turnstile>\<^sub>p\<langle>call init ei p return er c,Normal s\<rangle> \<Rightarrow>  u"
apply (simp add: call_def)
apply (rule exec_block)
apply  (erule (1) Call)
apply assumption
done


lemma exec_callAbrupt: 
 "\<lbrakk>\<Gamma> p=Some bdy;\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow>  Abrupt t\<rbrakk> 
  \<Longrightarrow> 
  \<Gamma>\<turnstile>\<^sub>p\<langle>call init ei p return er c,Normal s\<rangle> \<Rightarrow>  Abrupt (return s t)"
apply (simp add: call_def)
apply (rule exec_blockAbrupt)
apply (erule (1) Call)
done

lemma exec_callFault: 
             "\<lbrakk>\<Gamma> p=Some bdy; \<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow>  Fault f\<rbrakk> 
               \<Longrightarrow> 
              \<Gamma>\<turnstile>\<^sub>p\<langle>call init ei p return er c,Normal s\<rangle> \<Rightarrow>  Fault f"
apply (simp add: call_def)
apply (rule exec_blockFault)
apply (erule (1) Call)
done

lemma exec_callStuck: 
          "\<lbrakk>\<Gamma> p=Some bdy; \<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow>  Stuck\<rbrakk> 
           \<Longrightarrow> 
           \<Gamma>\<turnstile>\<^sub>p\<langle>call init ei p return er c,Normal s\<rangle> \<Rightarrow>  Stuck"
apply (simp add: call_def)
apply (rule exec_blockStuck)
apply (erule (1) Call)
done

lemma  exec_callUndefined: 
       "\<lbrakk>\<Gamma> p=None\<rbrakk> 
        \<Longrightarrow> 
        \<Gamma>\<turnstile>\<^sub>p\<langle>call init ei p return er c,Normal s\<rangle> \<Rightarrow>  Stuck"
apply (simp add: call_def)
apply (rule exec_blockStuck)
apply (erule CallUndefined)
done


lemma Fault_end: assumes exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>  t" and s: "s=Fault f" 
  shows "t=Fault f"
using exec s by (induct) auto

lemma Stuck_end: assumes exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>  t" and s: "s=Stuck" 
  shows "t=Stuck"
using exec s by (induct) auto

lemma Abrupt_end: assumes exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>  t" and s: "s=Abrupt s'" 
  shows "t=Abrupt s'"
using exec s by (induct) auto

lemma exec_Call_body_aux: 
  "\<Gamma> p=Some bdy \<Longrightarrow> 
   \<Gamma>\<turnstile>\<^sub>p\<langle>Call p,s\<rangle> \<Rightarrow> t = \<Gamma>\<turnstile>\<^sub>p\<langle>bdy,s\<rangle> \<Rightarrow> t"
apply (rule)
apply (fastforce elim: exec_elim_cases )
apply (cases s)
apply   (cases t)
apply (auto intro: exec.intros dest: Fault_end Stuck_end Abrupt_end)
done

lemma exec_Call_body':
  "p \<in> dom \<Gamma> \<Longrightarrow> 
  \<Gamma>\<turnstile>\<^sub>p\<langle>Call p,s\<rangle> \<Rightarrow> t = \<Gamma>\<turnstile>\<^sub>p\<langle>the (\<Gamma> p),s\<rangle> \<Rightarrow> t"
  apply clarsimp
  by (rule exec_Call_body_aux)



lemma exec_block_Normal_elim [consumes 1]:
assumes exec_block: "\<Gamma>\<turnstile>\<^sub>p\<langle>block init ei bdy return er c,Normal s\<rangle> \<Rightarrow>  t"
assumes Normal:
 "\<And>t'.
    \<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow>  Normal t';
     \<Gamma>\<turnstile>\<^sub>p\<langle>c s t',Normal (return s t')\<rangle> \<Rightarrow>  t\<rbrakk>
    \<Longrightarrow> P"
assumes Abrupt: 
 "\<And>t'.
    \<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow>  Abrupt t'; 
     t = Abrupt (return s t')\<rbrakk>
    \<Longrightarrow> P"
assumes Fault:
 "\<And>f.
    \<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow>  Fault f; 
     t = Fault f\<rbrakk>
    \<Longrightarrow> P"
assumes Stuck:
 "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow>  Stuck; 
     t = Stuck\<rbrakk>
    \<Longrightarrow> P"
assumes 
 "\<lbrakk>\<Gamma> p = None; t = Stuck\<rbrakk> \<Longrightarrow> P"
shows "P"
  using exec_block
apply (unfold block_def)
apply (elim exec_Normal_elim_cases)
apply simp_all
apply  (case_tac s')
apply     simp_all
apply     (elim exec_Normal_elim_cases)
apply     simp
apply    (drule Abrupt_end) apply simp 
apply    (erule exec_Normal_elim_cases)
apply    simp  
apply    (rule Abrupt,assumption+)
apply   (drule Fault_end) apply simp
apply   (erule exec_Normal_elim_cases)
apply   simp
apply  (drule Stuck_end) apply simp
apply  (erule exec_Normal_elim_cases)
apply  simp
apply (case_tac s')
apply    simp_all
apply   (elim exec_Normal_elim_cases)
apply   simp
apply   (rule Normal, assumption+)
apply  (drule Fault_end) apply simp
apply  (rule Fault,assumption+) 
apply (drule Stuck_end) apply simp
apply (rule Stuck,assumption+)
done

lemma exec_call_Normal_elim [consumes 1]:
assumes exec_call: "\<Gamma>\<turnstile>\<^sub>p\<langle>call init ei p return er c,Normal s\<rangle> \<Rightarrow>  t"
assumes Normal:
 "\<And>bdy t'.
    \<lbrakk>\<Gamma> p = Some bdy; \<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow>  Normal t';
     \<Gamma>\<turnstile>\<^sub>p\<langle>c s t',Normal (return s t')\<rangle> \<Rightarrow>  t\<rbrakk>
    \<Longrightarrow> P"
assumes Abrupt:
 "\<And>bdy t'.
    \<lbrakk>\<Gamma> p = Some bdy; \<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow>  Abrupt t'; 
     t = Abrupt (return s t')\<rbrakk>
    \<Longrightarrow> P"
assumes Fault:
 "\<And>bdy f.
    \<lbrakk>\<Gamma> p = Some bdy; \<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow>  Fault f; 
     t = Fault f\<rbrakk>
    \<Longrightarrow> P"
assumes Stuck:
 "\<And>bdy.
    \<lbrakk>\<Gamma> p = Some bdy; \<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow>  Stuck; 
     t = Stuck\<rbrakk>
    \<Longrightarrow> P"
assumes Undef:
 "\<lbrakk>\<Gamma> p = None; t = Stuck\<rbrakk> \<Longrightarrow> P"
shows "P"
  using exec_call
  apply (unfold call_def)
  apply (cases "\<Gamma> p")
  apply  (erule exec_block_Normal_elim)
  apply      (elim exec_Normal_elim_cases)
  apply       simp
  apply      simp
  apply     (elim exec_Normal_elim_cases)
  apply      simp
  apply     simp
  apply    (elim exec_Normal_elim_cases)
  apply     simp
  apply    simp
  apply   (elim exec_Normal_elim_cases)
  apply    simp
  apply   (rule Undef,assumption,assumption)
  apply  (rule Undef,assumption+)
  apply (erule exec_block_Normal_elim)
  apply     (elim exec_Normal_elim_cases)
  apply      simp
  apply      (rule Normal,assumption+)
  apply     simp
  apply    (elim exec_Normal_elim_cases)
  apply     simp
  apply     (rule Abrupt,assumption+)
  apply    simp
  apply   (elim exec_Normal_elim_cases)
  apply    simp
  apply   (rule Fault, assumption+)
  apply   simp
  apply  (elim exec_Normal_elim_cases)
  apply   simp
  apply  (rule Stuck,assumption,assumption,assumption)
  apply  simp
  apply (rule Undef,assumption+)
  done


lemma exec_dynCall:  
          "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>call init ei(p s) return er c,Normal s\<rangle> \<Rightarrow>  t\<rbrakk> 
           \<Longrightarrow> 
           \<Gamma>\<turnstile>\<^sub>p\<langle>dynCall init ei p return er c,Normal s\<rangle> \<Rightarrow>  t"
apply (simp add: dynCall_def)
by (rule DynCom)

lemma exec_dynCall_Normal_elim:
  assumes exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>dynCall init ei p return er c,Normal s\<rangle> \<Rightarrow>  t"
  assumes call: "\<Gamma>\<turnstile>\<^sub>p\<langle>call init ei (p s) return er c,Normal s\<rangle> \<Rightarrow>  t \<Longrightarrow> P"
  shows "P"
  using exec
  apply (simp add: dynCall_def)
  apply (erule exec_Normal_elim_cases)
  apply (rule call,assumption)
  done


lemma exec_Call_body: 
  "\<Gamma> p=Some bdy \<Longrightarrow> 
   \<Gamma>\<turnstile>\<^sub>p\<langle>Call p,s\<rangle> \<Rightarrow>  t = \<Gamma>\<turnstile>\<^sub>p\<langle>the (\<Gamma> p),s\<rangle> \<Rightarrow>  t"
apply (rule)
apply (fastforce elim: exec_elim_cases )
apply (cases s)
apply   (cases t)
apply (fastforce intro: exec.intros dest: Fault_end Abrupt_end Stuck_end)+
done

lemma exec_Seq': "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c1,s\<rangle> \<Rightarrow>  s'; \<Gamma>\<turnstile>\<^sub>p\<langle>c2,s'\<rangle> \<Rightarrow>  s''\<rbrakk>
             \<Longrightarrow>
             \<Gamma>\<turnstile>\<^sub>p\<langle>Seq c1 c2,s\<rangle> \<Rightarrow>  s''" 
  apply (cases s)
  apply    (fastforce intro: exec.intros)
  apply   (fastforce dest: Abrupt_end)
  apply  (fastforce dest: Fault_end)
  apply (fastforce dest: Stuck_end)
  done


lemma exec_assoc: "\<Gamma>\<turnstile>\<^sub>p\<langle>Seq c1 (Seq c2 c3),s\<rangle> \<Rightarrow>  t = \<Gamma>\<turnstile>\<^sub>p\<langle>Seq (Seq c1 c2) c3,s\<rangle> \<Rightarrow>  t"
  by (blast elim!: exec_elim_cases intro: exec_Seq' )



(* ************************************************************************* *)
subsection {* Big-Step Execution with Recursion Limit: @{text "\<Gamma>\<turnstile>\<langle>c, s\<rangle> =n\<Rightarrow> t"} *}
(* ************************************************************************* *)

inductive "execn"::"[('s,'p,'f,'e) body,('s,'p,'f,'e) com,('s,'f) xstate,nat,('s,'f) xstate] 
                      \<Rightarrow> bool" ("_\<turnstile>\<^sub>p \<langle>_,_\<rangle> =_\<Rightarrow> _"  [60,20,98,65,98] 89)
  for \<Gamma>::"('s,'p,'f,'e) body"
where
  Skip: "\<Gamma>\<turnstile>\<^sub>p\<langle>Skip,Normal s\<rangle> =n\<Rightarrow>  Normal s"
| Guard: "\<lbrakk>s\<in>g; \<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow>  t\<rbrakk> 
          \<Longrightarrow> 
          \<Gamma>\<turnstile>\<^sub>p\<langle>Guard f g c,Normal s\<rangle> =n\<Rightarrow>  t"

| GuardFault: "s\<notin>g \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>Guard f g c,Normal s\<rangle> =n\<Rightarrow>  Fault f"

| FaultProp [intro,simp]: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Fault f\<rangle> =n\<Rightarrow>  Fault f" 

| Basic: "\<Gamma>\<turnstile>\<^sub>p\<langle>Basic f e,Normal s\<rangle> =n\<Rightarrow>  Normal (f s)"

| Spec: "(s,t) \<in> r 
         \<Longrightarrow> 
         \<Gamma>\<turnstile>\<^sub>p\<langle>Spec r e,Normal s\<rangle> =n\<Rightarrow>  Normal t"

| SpecStuck: "\<forall>t. (s,t) \<notin> r 
              \<Longrightarrow> 
              \<Gamma>\<turnstile>\<^sub>p\<langle>Spec r e,Normal s\<rangle> =n\<Rightarrow>  Stuck"

| Seq: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c\<^sub>1,Normal s\<rangle> =n\<Rightarrow>  s'; \<Gamma>\<turnstile>\<^sub>p\<langle>c\<^sub>2,s'\<rangle> =n\<Rightarrow>  t\<rbrakk>
        \<Longrightarrow>
        \<Gamma>\<turnstile>\<^sub>p\<langle>Seq c\<^sub>1 c\<^sub>2,Normal s\<rangle> =n\<Rightarrow>  t" 

| CondTrue: "\<lbrakk>s \<in> b; \<Gamma>\<turnstile>\<^sub>p\<langle>c\<^sub>1,Normal s\<rangle> =n\<Rightarrow>  t\<rbrakk> 
             \<Longrightarrow>  
             \<Gamma>\<turnstile>\<^sub>p\<langle>Cond b c\<^sub>1 c\<^sub>2,Normal s\<rangle> =n\<Rightarrow>  t"

| CondFalse: "\<lbrakk>s \<notin> b; \<Gamma>\<turnstile>\<^sub>p\<langle>c\<^sub>2,Normal s\<rangle> =n\<Rightarrow>  t\<rbrakk> 
              \<Longrightarrow>  
              \<Gamma>\<turnstile>\<^sub>p\<langle>Cond b c\<^sub>1 c\<^sub>2,Normal s\<rangle> =n\<Rightarrow>  t"

| WhileTrue: "\<lbrakk>s \<in> b; \<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow>  s'; 
              \<Gamma>\<turnstile>\<^sub>p\<langle>While b c,s'\<rangle> =n\<Rightarrow>  t\<rbrakk> 
              \<Longrightarrow>  
              \<Gamma>\<turnstile>\<^sub>p\<langle>While b c,Normal s\<rangle> =n\<Rightarrow>  t"

| WhileFalse: "\<lbrakk>s \<notin> b\<rbrakk> 
               \<Longrightarrow>  
               \<Gamma>\<turnstile>\<^sub>p\<langle>While b c,Normal s\<rangle> =n\<Rightarrow>  Normal s"

| AwaitTrue: "\<lbrakk>s \<in> b;  \<Gamma>1=\<Gamma>\<^sub>\<not>\<^sub>a ;\<Gamma>1\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow>t\<rbrakk> 
              \<Longrightarrow>  
              \<Gamma>\<turnstile>\<^sub>p\<langle>Await b c e,Normal s\<rangle> =n\<Rightarrow>t"
| AwaitFalse: "\<lbrakk>s \<notin> b\<rbrakk> 
              \<Longrightarrow>  
              \<Gamma>\<turnstile>\<^sub>p\<langle>Await b ca e,Normal s\<rangle>  =n\<Rightarrow>  Normal s"

| Call:  "\<lbrakk>\<Gamma> p=Some bdy;\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal s\<rangle> =n\<Rightarrow>  t\<rbrakk> 
          \<Longrightarrow> 
          \<Gamma>\<turnstile>\<^sub>p\<langle>Call p ,Normal s\<rangle> =Suc n\<Rightarrow>  t"
 
| CallUndefined: "\<lbrakk>\<Gamma> p=None\<rbrakk> 
                 \<Longrightarrow> 
                 \<Gamma>\<turnstile>\<^sub>p\<langle>Call p ,Normal s\<rangle> =Suc n\<Rightarrow>  Stuck"

| StuckProp [intro,simp]: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Stuck\<rangle> =n\<Rightarrow>  Stuck"
 
| DynCom:  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>(c s),Normal s\<rangle> =n\<Rightarrow>  t\<rbrakk> 
             \<Longrightarrow> 
             \<Gamma>\<turnstile>\<^sub>p\<langle>DynCom c,Normal s\<rangle> =n\<Rightarrow>  t"

| Throw: "\<Gamma>\<turnstile>\<^sub>p\<langle>Throw,Normal s\<rangle> =n\<Rightarrow>  Abrupt s"

| AbruptProp [intro,simp]: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Abrupt s\<rangle> =n\<Rightarrow>  Abrupt s"
  
| CatchMatch: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c\<^sub>1,Normal s\<rangle> =n\<Rightarrow>  Abrupt s'; \<Gamma>\<turnstile>\<^sub>p\<langle>c\<^sub>2,Normal s'\<rangle> =n\<Rightarrow> t\<rbrakk>
               \<Longrightarrow>
               \<Gamma>\<turnstile>\<^sub>p\<langle>Catch c\<^sub>1 c\<^sub>2,Normal s\<rangle> =n\<Rightarrow> t" 
| CatchMiss: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c\<^sub>1,Normal s\<rangle> =n\<Rightarrow>  t; \<not>isAbr t\<rbrakk>
               \<Longrightarrow>
               \<Gamma>\<turnstile>\<^sub>p\<langle>Catch c\<^sub>1 c\<^sub>2,Normal s\<rangle> =n\<Rightarrow>  t"
 
inductive_cases execn_elim_cases [cases set]:
  "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Fault f\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Stuck\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Abrupt s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Skip,s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Seq c1 c2,s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Guard f g c,s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Basic f e,s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Spec r e,s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Cond b c1 c2,s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Await b c e,s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Call p ,s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>DynCom c,s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Throw,s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Catch c1 c2,s\<rangle> =n\<Rightarrow>  t"


inductive_cases execn_Normal_elim_cases [cases set]: 
  "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Fault f\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Stuck\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Abrupt s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Skip,Normal s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Guard f g c,Normal s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Basic f e,Normal s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Spec r e,Normal s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Seq c1 c2,Normal s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Cond b c1 c2,Normal s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,Normal s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Await b c e,Normal s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Call p,Normal s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>DynCom c,Normal s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Throw,Normal s\<rangle> =n\<Rightarrow>  t"
  "\<Gamma>\<turnstile>\<^sub>p\<langle>Catch c1 c2,Normal s\<rangle> =n\<Rightarrow>  t"

lemma execn_Skip': "\<Gamma>\<turnstile>\<^sub>p\<langle>Skip,t\<rangle> =n\<Rightarrow> t"
  by (cases t) (auto intro: execn.intros)

lemma execn_Fault_end: assumes exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>  t" and s: "s=Fault f" 
  shows "t=Fault f"
using exec s by (induct) auto

lemma execn_Stuck_end: assumes exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>  t" and s: "s=Stuck" 
  shows "t=Stuck"
using exec s by (induct) auto

lemma execn_Abrupt_end: assumes exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>  t" and s: "s=Abrupt s'" 
  shows "t=Abrupt s'"
using exec s by (induct) auto

lemma execn_block: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> =n\<Rightarrow>  Normal t; \<Gamma>\<turnstile>\<^sub>p\<langle>c s t,Normal (return s t)\<rangle> =n\<Rightarrow>  u\<rbrakk>
  \<Longrightarrow> 
  \<Gamma>\<turnstile>\<^sub>p\<langle>block init ei bdy return er c,Normal s\<rangle> =n\<Rightarrow>  u"
apply (unfold block_def)
by (fastforce intro: execn.intros)

lemma execn_blockAbrupt: 
     "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> =n\<Rightarrow>  Abrupt t\<rbrakk>
       \<Longrightarrow> 
       \<Gamma>\<turnstile>\<^sub>p\<langle>block init ei bdy return er c,Normal s\<rangle> =n\<Rightarrow>  Abrupt (return s t)"
apply (unfold block_def)
by (fastforce intro: execn.intros)

lemma execn_blockFault: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> =n\<Rightarrow>  Fault f\<rbrakk>
   \<Longrightarrow> 
  \<Gamma>\<turnstile>\<^sub>p\<langle>block init ei bdy return er c,Normal s\<rangle> =n\<Rightarrow>  Fault f"
apply (unfold block_def)
by (fastforce intro: execn.intros)

lemma execn_blockStuck:
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> =n\<Rightarrow>  Stuck\<rbrakk>
  \<Longrightarrow> 
  \<Gamma>\<turnstile>\<^sub>p\<langle>block init ei bdy return er c,Normal s\<rangle> =n\<Rightarrow>  Stuck"
apply (unfold block_def)
by (fastforce intro: execn.intros)


lemma execn_call:   
 "\<lbrakk>\<Gamma> p=Some bdy;\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> =n\<Rightarrow>  Normal t; 
   \<Gamma>\<turnstile>\<^sub>p\<langle>c s t,Normal (return s t)\<rangle> =Suc n\<Rightarrow>  u\<rbrakk> 
  \<Longrightarrow> 
  \<Gamma>\<turnstile>\<^sub>p\<langle>call init ei p return er c,Normal s\<rangle> =Suc n\<Rightarrow>  u"
apply (simp add: call_def)
apply (rule execn_block)
apply  (erule (1) Call)
apply assumption
done


lemma execn_callAbrupt: 
 "\<lbrakk>\<Gamma> p=Some bdy;\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> =n\<Rightarrow>  Abrupt t\<rbrakk> 
  \<Longrightarrow> 
  \<Gamma>\<turnstile>\<^sub>p\<langle>call init ei p return er c,Normal s\<rangle> =Suc n\<Rightarrow>  Abrupt (return s t)"
apply (simp add: call_def)
apply (rule execn_blockAbrupt)
apply (erule (1) Call)
done

lemma execn_callFault: 
             "\<lbrakk>\<Gamma> p=Some bdy; \<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> =n\<Rightarrow>  Fault f\<rbrakk> 
               \<Longrightarrow> 
              \<Gamma>\<turnstile>\<^sub>p\<langle>call init ei p return er c,Normal s\<rangle> =Suc n\<Rightarrow>  Fault f"
apply (simp add: call_def)
apply (rule execn_blockFault)
apply (erule (1) Call)
done

lemma execn_callStuck: 
          "\<lbrakk>\<Gamma> p=Some bdy; \<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> =n\<Rightarrow>  Stuck\<rbrakk> 
           \<Longrightarrow> 
           \<Gamma>\<turnstile>\<^sub>p\<langle>call init ei p return er c,Normal s\<rangle> =Suc n\<Rightarrow>  Stuck"
apply (simp add: call_def)
apply (rule execn_blockStuck)
apply (erule (1) Call)
done

lemma  execn_callUndefined: 
       "\<lbrakk>\<Gamma> p=None\<rbrakk> 
        \<Longrightarrow> 
        \<Gamma>\<turnstile>\<^sub>p\<langle>call init ei p return er c,Normal s\<rangle> =Suc n\<Rightarrow>  Stuck"
apply (simp add: call_def)
apply (rule execn_blockStuck)
apply (erule CallUndefined)
done

lemma execn_block_Normal_elim [consumes 1]:
assumes execn_block: "\<Gamma>\<turnstile>\<^sub>p\<langle>block init ei bdy return er c,Normal s\<rangle> =n\<Rightarrow>  t"
assumes Normal: 
 "\<And>t'.
    \<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> =n\<Rightarrow>  Normal t';
     \<Gamma>\<turnstile>\<^sub>p\<langle>c s t',Normal (return s t')\<rangle> =n\<Rightarrow>  t\<rbrakk>
    \<Longrightarrow> P"
assumes Abrupt:
 "\<And>t'.
    \<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> =n\<Rightarrow>  Abrupt t'; 
     t = Abrupt (return s t')\<rbrakk>
    \<Longrightarrow> P"
assumes Fault:
 "\<And>f.
    \<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> =n\<Rightarrow>  Fault f; 
     t = Fault f\<rbrakk>
    \<Longrightarrow> P"
assumes Stuck:
 "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> =n\<Rightarrow>  Stuck; 
     t = Stuck\<rbrakk>
    \<Longrightarrow> P"
assumes Undef:
 "\<lbrakk>\<Gamma> p = None; t = Stuck\<rbrakk> \<Longrightarrow> P"
shows "P"
  using execn_block
apply (unfold block_def)
apply (elim execn_Normal_elim_cases)
apply simp_all
apply  (case_tac s')
apply     simp_all
apply     (elim execn_Normal_elim_cases)
apply     simp
apply    (drule execn_Abrupt_end) apply simp 
apply    (erule execn_Normal_elim_cases)
apply    simp
apply    (rule Abrupt,assumption+)
apply   (drule execn_Fault_end) apply simp
apply   (erule execn_Normal_elim_cases)
apply   simp
apply  (drule execn_Stuck_end) apply simp
apply  (erule execn_Normal_elim_cases)
apply  simp
apply (case_tac s')
apply    simp_all
apply   (elim execn_Normal_elim_cases)
apply   simp
apply   (rule Normal,assumption+)
apply  (drule execn_Fault_end) apply simp
apply  (rule Fault,assumption+)
apply (drule execn_Stuck_end) apply simp
apply (rule Stuck,assumption+)
done

lemma execn_call_Normal_elim [consumes 1]:
assumes exec_call: "\<Gamma>\<turnstile>\<^sub>p\<langle>call init ei p return er c,Normal s\<rangle> =n\<Rightarrow>  t"
assumes Normal:
 "\<And>bdy i t'.
    \<lbrakk>\<Gamma> p = Some bdy; \<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> =i\<Rightarrow>  Normal t'; 
     \<Gamma>\<turnstile>\<^sub>p\<langle>c s t',Normal (return s t')\<rangle> =Suc i\<Rightarrow>  t; n = Suc i\<rbrakk>
    \<Longrightarrow> P"
assumes Abrupt:
 "\<And>bdy i t'.
    \<lbrakk>\<Gamma> p = Some bdy; \<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> =i\<Rightarrow>  Abrupt t'; n = Suc i;
     t = Abrupt (return s t')\<rbrakk>
    \<Longrightarrow> P"
assumes Fault:
 "\<And>bdy i f.
    \<lbrakk>\<Gamma> p = Some bdy; \<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> =i\<Rightarrow>  Fault f; n = Suc i;
     t = Fault f\<rbrakk>
    \<Longrightarrow> P"
assumes Stuck:
 "\<And>bdy i.
    \<lbrakk>\<Gamma> p = Some bdy; \<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal (init s)\<rangle> =i\<Rightarrow>  Stuck; n = Suc i;
     t = Stuck\<rbrakk>
    \<Longrightarrow> P"
assumes Undef:
 "\<And>i. \<lbrakk>\<Gamma> p = None; n = Suc i; t = Stuck\<rbrakk> \<Longrightarrow> P"
shows "P"
  using exec_call
  apply (unfold call_def)
  apply (cases n)
  apply  (simp only: block_def)
  apply  (fastforce elim: execn_Normal_elim_cases)
  apply (cases "\<Gamma> p")
  apply  (erule execn_block_Normal_elim)
  apply      (elim execn_Normal_elim_cases)
  apply       simp
  apply      simp
  apply     (elim execn_Normal_elim_cases)
  apply      simp
  apply     simp
  apply    (elim execn_Normal_elim_cases)
  apply     simp
  apply    simp
  apply   (elim execn_Normal_elim_cases)
  apply    simp
  apply   (rule Undef,assumption,assumption,assumption)
  apply  (rule Undef,assumption+)
  apply (erule execn_block_Normal_elim)
  apply     (elim execn_Normal_elim_cases)
  apply      simp
  apply      (rule Normal,assumption+)
  apply     simp
  apply    (elim execn_Normal_elim_cases)
  apply     simp
  apply     (rule Abrupt,assumption+)
  apply    simp
  apply   (elim execn_Normal_elim_cases)
  apply    simp
  apply   (rule Fault,assumption+)
  apply   simp
  apply  (elim execn_Normal_elim_cases)
  apply   simp
  apply  (rule Stuck,assumption,assumption,assumption,assumption)
  apply  (rule Undef,assumption,assumption,assumption)
  apply (rule Undef,assumption+)
  done

lemma execn_dynCall:  
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>call init ei (p s) return er c,Normal s\<rangle> =n\<Rightarrow>  t\<rbrakk> 
  \<Longrightarrow> 
  \<Gamma>\<turnstile>\<^sub>p\<langle>dynCall init ei p return er c,Normal s\<rangle> =n\<Rightarrow>  t"
apply (simp add: dynCall_def)
by (rule DynCom)

lemma execn_dynCall_Normal_elim:
  assumes exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>dynCall init ei p return er c,Normal s\<rangle> =n\<Rightarrow>  t"
  assumes "\<Gamma>\<turnstile>\<^sub>p\<langle>call init ei (p s) return er c,Normal s\<rangle> =n\<Rightarrow>  t \<Longrightarrow> P"
  shows "P"
  using exec
  apply (simp add: dynCall_def)
  apply (erule execn_Normal_elim_cases)
  apply fact
  done

lemma  execn_Seq': 
       "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c1,s\<rangle> =n\<Rightarrow>  s'; \<Gamma>\<turnstile>\<^sub>p\<langle>c2,s'\<rangle> =n\<Rightarrow>  s''\<rbrakk>
        \<Longrightarrow>
        \<Gamma>\<turnstile>\<^sub>p\<langle>Seq c1 c2,s\<rangle> =n\<Rightarrow>  s''"
  apply (cases s)
  apply    (fastforce intro: execn.intros)
  apply   (fastforce dest: execn_Abrupt_end)
  apply  (fastforce dest: execn_Fault_end)
  apply (fastforce dest: execn_Stuck_end)
  done
thm execn.intros
lemma execn_mono:
 assumes exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>  t"
  shows "\<And> m. n \<le> m \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =m\<Rightarrow>  t"
using exec
by (induct)(auto intro: execn.intros Semantic.execn_mono dest: Suc_le_D)
 

lemma execn_Suc: 
  "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>  t \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =Suc n\<Rightarrow>  t"
  by (rule execn_mono [OF _ le_refl [THEN le_SucI]])

lemma execn_assoc: 
 "\<Gamma>\<turnstile>\<^sub>p\<langle>Seq c1 (Seq c2 c3),s\<rangle> =n\<Rightarrow>  t = \<Gamma>\<turnstile>\<^sub>p\<langle>Seq (Seq c1 c2) c3,s\<rangle> =n\<Rightarrow>  t"
  by (auto elim!: execn_elim_cases intro: execn_Seq')


lemma execn_to_exec: 
  assumes execn: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>  t"
  shows "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t"
using execn
by (induct)(auto intro: exec.intros Semantic.execn_to_exec)
        
lemma exec_to_execn: 
  assumes execn: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t"
  shows "\<exists>n. \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>  t"
using execn
proof (induct)
  case Skip thus ?case by (iprover intro: execn.intros)
next
  case Guard thus ?case by (iprover intro: execn.intros)
next
  case GuardFault thus ?case by (iprover intro: execn.intros)
next
 case FaultProp thus ?case by (iprover intro: execn.intros)
next
  case Basic thus ?case by (iprover intro: execn.intros)
next
  case Spec thus ?case by (iprover intro: execn.intros)
next
  case SpecStuck thus ?case by (iprover intro: execn.intros)
next
  case (Seq c1 s s' c2 s'')
  then obtain n m where
    "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> =n\<Rightarrow>  s'" "\<Gamma>\<turnstile>\<^sub>p\<langle>c2,s'\<rangle> =m\<Rightarrow>  s''"
    by blast
  then have 
    "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> =max n m\<Rightarrow>  s'" 
    "\<Gamma>\<turnstile>\<^sub>p\<langle>c2,s'\<rangle> =max n m\<Rightarrow>  s''"
    by (auto elim!: execn_mono intro: max.cobounded1 max.cobounded2)
  thus ?case 
    by (iprover intro: execn.intros)
next
  case CondTrue thus ?case by (iprover intro: execn.intros)
next
  case CondFalse thus ?case by (iprover intro: execn.intros)
next
  case (WhileTrue s b c s' s'') 
  then obtain n m where
    "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow>  s'" "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,s'\<rangle> =m\<Rightarrow>  s''"
    by blast
  then have 
    "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =max n m\<Rightarrow>  s'" "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,s'\<rangle> =max n m\<Rightarrow>  s''"
    by (auto elim!: execn_mono intro: max.cobounded1 max.cobounded2)
  with WhileTrue
  show ?case
    by (iprover intro: execn.intros)
next
  case WhileFalse thus ?case by (iprover intro: execn.intros)
next
  case Call thus ?case by (iprover intro: execn.intros)
next
  case CallUndefined thus ?case by (iprover intro: execn.intros)
next
  case StuckProp thus ?case by (iprover intro: execn.intros)
next
  case DynCom thus ?case by (iprover intro: execn.intros)
next
  case Throw thus ?case by (iprover intro: execn.intros)
next
  case AbruptProp thus ?case by (iprover intro: execn.intros)
next
  case (CatchMatch c1 s s' c2 s'')
  then obtain n m where
    "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> =n\<Rightarrow>  Abrupt s'" "\<Gamma>\<turnstile>\<^sub>p\<langle>c2,Normal s'\<rangle> =m\<Rightarrow>  s''"
    by blast
  then have 
    "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> =max n m\<Rightarrow>  Abrupt s'" 
    "\<Gamma>\<turnstile>\<^sub>p\<langle>c2,Normal s'\<rangle> =max n m\<Rightarrow>  s''"
    by (auto elim!: execn_mono intro: max.cobounded1 max.cobounded2)
  with CatchMatch.hyps show ?case 
    by (iprover intro: execn.intros)
next
  case CatchMiss thus ?case by (iprover intro: execn.intros)
next
  case (AwaitTrue s b c t) thus ?case by (meson exec_to_execn execn.intros )
next 
  case (AwaitFalse s b ca) thus ?case by (meson exec_to_execn execn.intros )
qed 


theorem exec_iff_execn: "(\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t) = (\<exists>n. \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t)"
  by (iprover intro: exec_to_execn execn_to_exec)


definition nfinal_notin:: "('s,'p,'f,'e) body \<Rightarrow> ('s,'p,'f,'e) com \<Rightarrow> ('s,'f) xstate \<Rightarrow>  nat 
                       \<Rightarrow> ('s,'f) xstate set \<Rightarrow> bool"
  ("_\<turnstile>\<^sub>p \<langle>_,_\<rangle> =_\<Rightarrow>\<notin>_"  [60,20,98,65,60] 89) where
"\<Gamma>\<turnstile>\<^sub>p \<langle>c,s\<rangle> =n\<Rightarrow>\<notin>T = (\<forall>t. \<Gamma>\<turnstile>\<^sub>p \<langle>c,s\<rangle> =n\<Rightarrow> t \<longrightarrow> t\<notin>T)"

definition final_notin:: "('s,'p,'f,'e) body \<Rightarrow> ('s,'p,'f,'e) com \<Rightarrow> ('s,'f) xstate  
                       \<Rightarrow> ('s,'f) xstate set \<Rightarrow> bool"
  ("_\<turnstile>\<^sub>p \<langle>_,_\<rangle> \<Rightarrow>\<notin>_"  [60,20,98,60] 89) where
"\<Gamma>\<turnstile>\<^sub>p \<langle>c,s\<rangle> \<Rightarrow>\<notin>T = (\<forall>t. \<Gamma>\<turnstile>\<^sub>p \<langle>c,s\<rangle> \<Rightarrow>t \<longrightarrow> t\<notin>T)"

lemma final_notinI: "\<lbrakk>\<And>t. \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t \<Longrightarrow> t \<notin> T\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>\<notin>T"
  by (simp add: final_notin_def)

lemma noFaultStuck_Call_body': "p \<in> dom \<Gamma> \<Longrightarrow>
\<Gamma>\<turnstile>\<^sub>p\<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) =
\<Gamma>\<turnstile>\<^sub>p\<langle>the (\<Gamma> p),Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
  by (clarsimp simp add: final_notin_def exec_Call_body)

lemma noFault_startn: 
  assumes execn: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" and t: "t\<noteq>Fault f" 
  shows "s\<noteq>Fault f"
using execn t by (induct) auto

lemma noFault_start: 
  assumes exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t" and t: "t\<noteq>Fault f" 
  shows "s\<noteq>Fault f"
using exec t by (induct) auto

lemma noStuck_startn: 
  assumes execn: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" and t: "t\<noteq>Stuck" 
  shows "s\<noteq>Stuck"
using execn t by (induct) auto

lemma noStuck_start: 
  assumes exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t" and t: "t\<noteq>Stuck" 
  shows "s\<noteq>Stuck"
using exec t by (induct) auto

lemma noAbrupt_startn: 
  assumes execn: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" and t: "\<forall>t'. t\<noteq>Abrupt t'" 
  shows "s\<noteq>Abrupt s'"
using execn t by (induct) auto

lemma noAbrupt_start: 
  assumes exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t" and t: "\<forall>t'. t\<noteq>Abrupt t'" 
  shows "s\<noteq>Abrupt s'"
using exec t by (induct) auto

lemma noFaultn_startD: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> Normal t \<Longrightarrow> s \<noteq> Fault f"
  by (auto dest: noFault_startn)

lemma noFaultn_startD': "t\<noteq>Fault f \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t \<Longrightarrow> s \<noteq> Fault f"
  by (auto dest: noFault_startn)

lemma noFault_startD: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> Normal t \<Longrightarrow> s \<noteq> Fault f"
  by (auto dest: noFault_start)

lemma noFault_startD': "t\<noteq>Fault f\<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t \<Longrightarrow> s \<noteq> Fault f"
  by (auto dest: noFault_start)

lemma noStuckn_startD: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> Normal t \<Longrightarrow> s \<noteq> Stuck"
  by (auto dest: noStuck_startn)

lemma noStuckn_startD': "t\<noteq>Stuck \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t \<Longrightarrow> s \<noteq> Stuck"
  by (auto dest: noStuck_startn)

lemma noStuck_startD: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> Normal t \<Longrightarrow> s \<noteq> Stuck"
  by (auto dest: noStuck_start)

lemma noStuck_startD': "t\<noteq>Stuck \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t \<Longrightarrow> s \<noteq> Stuck"
  by (auto dest: noStuck_start)

lemma noAbruptn_startD: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> Normal t \<Longrightarrow> s \<noteq> Abrupt s'"
  by (auto dest: noAbrupt_startn)

lemma noAbrupt_startD: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> Normal t \<Longrightarrow> s \<noteq> Abrupt s'"
  by (auto dest: noAbrupt_start)

lemma noFaultnI: "\<lbrakk>\<And>t. \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>t \<Longrightarrow> t\<noteq>Fault f\<rbrakk> \<Longrightarrow>  \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>\<notin>{Fault f}" 
  by (simp add: nfinal_notin_def)

lemma noFaultnI': 
  assumes contr: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> Fault f \<Longrightarrow> False"
  shows "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>\<notin>{Fault f}"
  proof (rule noFaultnI)
    fix t assume "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" 
    with contr show "t \<noteq> Fault f"
      by (cases "t=Fault f") auto
  qed

lemma noFaultn_def': "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>\<notin>{Fault f} = (\<not>\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> Fault f)"
  apply rule
  apply  (fastforce simp add: nfinal_notin_def)
  apply (fastforce intro: noFaultnI')
  done

lemma noStucknI: "\<lbrakk>\<And>t. \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>t \<Longrightarrow> t\<noteq>Stuck\<rbrakk> \<Longrightarrow>  \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>\<notin>{Stuck}" 
  by (simp add: nfinal_notin_def)

lemma noStucknI': 
  assumes contr: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> Stuck \<Longrightarrow> False"
  shows "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>\<notin>{Stuck}"
  proof (rule noStucknI)
    fix t assume "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" 
    with contr show "t \<noteq> Stuck"
      by (cases t) auto
  qed

lemma noStuckn_def': "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>\<notin>{Stuck} = (\<not>\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> Stuck)"
  apply rule
  apply  (fastforce simp add: nfinal_notin_def)
  apply (fastforce intro: noStucknI')
  done


lemma noFaultI: "\<lbrakk>\<And>t. \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>t \<Longrightarrow> t\<noteq>Fault f\<rbrakk> \<Longrightarrow>  \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>\<notin>{Fault f}" 
  by (simp add: final_notin_def)

lemma noFaultI': 
  assumes contr: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> Fault f\<Longrightarrow> False"
  shows "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>\<notin>{Fault f}"
  proof (rule noFaultI)
    fix t assume "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t" 
    with contr show "t \<noteq> Fault f"
      by (cases "t=Fault f") auto
  qed

lemma noFaultE: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>\<notin>{Fault f}; \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> Fault f\<rbrakk> \<Longrightarrow> P"
  by (auto simp add: final_notin_def)
 
lemma noFault_def': "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>\<notin>{Fault f} = (\<not>\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> Fault f)"
  apply rule
  apply  (fastforce simp add: final_notin_def)
  apply (fastforce intro: noFaultI')
  done


lemma noStuckI: "\<lbrakk>\<And>t. \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>t \<Longrightarrow> t\<noteq>Stuck\<rbrakk> \<Longrightarrow>  \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>\<notin>{Stuck}" 
  by (simp add: final_notin_def)

lemma noStuckI': 
  assumes contr: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> Stuck \<Longrightarrow> False"
  shows "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>\<notin>{Stuck}"
  proof (rule noStuckI)
    fix t assume "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t" 
    with contr show "t \<noteq> Stuck"
      by (cases t) auto
  qed

lemma noStuckE: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>\<notin>{Stuck}; \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> Stuck\<rbrakk> \<Longrightarrow> P"
  by (auto simp add: final_notin_def)
 
lemma noStuck_def': "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>\<notin>{Stuck} = (\<not>\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> Stuck)"
  apply rule
  apply  (fastforce simp add: final_notin_def)
  apply (fastforce intro: noStuckI')
  done


lemma noFaultn_execD: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>\<notin>{Fault f}; \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>t\<rbrakk> \<Longrightarrow> t\<noteq>Fault f"
  by (simp add: nfinal_notin_def)

lemma noFault_execD: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>\<notin>{Fault f}; \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>t\<rbrakk> \<Longrightarrow> t\<noteq>Fault f"
  by (simp add: final_notin_def)

lemma noFaultn_exec_startD: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>\<notin>{Fault f}; \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>t\<rbrakk> \<Longrightarrow> s\<noteq>Fault f"
  by (auto simp add: nfinal_notin_def dest: noFaultn_startD)

lemma noFault_exec_startD: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>\<notin>{Fault f}; \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>t\<rbrakk> \<Longrightarrow> s\<noteq>Fault f"
  by (auto simp add: final_notin_def dest: noFault_startD)

lemma noStuckn_execD: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>\<notin>{Stuck}; \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>t\<rbrakk> \<Longrightarrow> t\<noteq>Stuck"
  by (simp add: nfinal_notin_def)

lemma noStuck_execD: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>\<notin>{Stuck}; \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>t\<rbrakk> \<Longrightarrow> t\<noteq>Stuck"
  by (simp add: final_notin_def)

lemma noStuckn_exec_startD: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>\<notin>{Stuck}; \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>t\<rbrakk> \<Longrightarrow> s\<noteq>Stuck"
  by (auto simp add: nfinal_notin_def dest: noStuckn_startD)

lemma noStuck_exec_startD: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>\<notin>{Stuck}; \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>t\<rbrakk> \<Longrightarrow> s\<noteq>Stuck"
  by (auto simp add: final_notin_def dest: noStuck_startD)

lemma noFaultStuckn_execD: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>\<notin>{Fault True,Fault False,Stuck}; \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>t\<rbrakk> \<Longrightarrow> 
       t\<notin>{Fault True,Fault False,Stuck}"
  by (simp add: nfinal_notin_def)

lemma noFaultStuck_execD: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>\<notin>{Fault True,Fault False,Stuck}; \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>t\<rbrakk> 
 \<Longrightarrow> t\<notin>{Fault True,Fault False,Stuck}"
  by (simp add: final_notin_def)

lemma noFaultStuckn_exec_startD: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>\<notin>{Fault True, Fault False,Stuck}; \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>t\<rbrakk> 
   \<Longrightarrow> s\<notin>{Fault True,Fault False,Stuck}"
  by (auto simp add: nfinal_notin_def )

lemma noFaultStuck_exec_startD: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>\<notin>{Fault True, Fault False,Stuck}; \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>t\<rbrakk> 
  \<Longrightarrow> s\<notin>{Fault True,Fault False,Stuck}"
  by (auto simp add: final_notin_def )

lemma noStuck_Call: 
  assumes noStuck: "\<Gamma>\<turnstile>\<^sub>p\<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}"
  shows "p \<in> dom \<Gamma>"
proof (cases "p \<in> dom \<Gamma>")
  case True thus ?thesis by simp
next
  case False
  hence "\<Gamma> p = None" by auto 
  hence "\<Gamma>\<turnstile>\<^sub>p\<langle>Call p,Normal s\<rangle> \<Rightarrow>Stuck"
    by (rule exec.CallUndefined)
  with noStuck show ?thesis
    by (auto simp add: final_notin_def)
qed


lemma Guard_noFaultStuckD: 
  assumes "\<Gamma>\<turnstile>\<^sub>p\<langle>Guard f g c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
  assumes "f \<notin> F"
  shows "s \<in> g"
  using assms
  by (auto simp add: final_notin_def intro: exec.intros)


lemma final_notin_to_finaln:  
  assumes notin: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>\<notin>T"
  shows "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>\<notin>T"
proof (clarsimp simp add: nfinal_notin_def)
  fix t assume "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" and "t\<in>T"
  with notin show "False"
    by (auto intro: execn_to_exec simp add: final_notin_def)
qed

lemma noFault_Call_body: 
"\<Gamma> p=Some bdy\<Longrightarrow>
 \<Gamma>\<turnstile>\<^sub>p\<langle>Call p ,Normal s\<rangle> \<Rightarrow>\<notin>{Fault f} = 
 \<Gamma>\<turnstile>\<^sub>p\<langle>the (\<Gamma> p),Normal s\<rangle> \<Rightarrow>\<notin>{Fault f}"
  by (simp add: noFault_def' exec_Call_body)

lemma noStuck_Call_body: 
"\<Gamma> p=Some bdy\<Longrightarrow>
 \<Gamma>\<turnstile>\<^sub>p\<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck} = 
 \<Gamma>\<turnstile>\<^sub>p\<langle>the (\<Gamma> p),Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}"
  by (simp add: noStuck_def' exec_Call_body)

lemma exec_final_notin_to_execn: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>\<notin>T \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>\<notin>T"
  by (auto simp add: final_notin_def nfinal_notin_def dest: execn_to_exec)

lemma execn_final_notin_to_exec: "\<forall>n. \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>\<notin>T \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>\<notin>T"
  by (auto simp add: final_notin_def nfinal_notin_def dest: exec_to_execn)

lemma exec_final_notin_iff_execn: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow>\<notin>T = (\<forall>n. \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>\<notin>T)"
  by (auto intro: exec_final_notin_to_execn execn_final_notin_to_exec)

lemma Seq_NoFaultStuckD2: 
  assumes noabort: "\<Gamma>\<turnstile>\<^sub>p\<langle>Seq c1 c2,s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault `  F)"
  shows "\<forall>t. \<Gamma>\<turnstile>\<^sub>p\<langle>c1,s\<rangle> \<Rightarrow> t \<longrightarrow> t\<notin> ({Stuck} \<union> Fault `  F) \<longrightarrow> 
             \<Gamma>\<turnstile>\<^sub>p\<langle>c2,t\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault `  F)"
using noabort
by (auto simp add: final_notin_def intro: exec_Seq') lemma Seq_NoFaultStuckD1: 
  assumes noabort: "\<Gamma>\<turnstile>\<^sub>p\<langle>Seq c1 c2,s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault `  F)"
  shows "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault `  F)"
proof (rule final_notinI)
  fix t
  assume exec_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,s\<rangle> \<Rightarrow> t"
  show "t \<notin> {Stuck} \<union> Fault `  F"
  proof 
    assume "t \<in> {Stuck} \<union> Fault `  F"
    moreover
    {
      assume "t = Stuck"
      with exec_c1
      have "\<Gamma>\<turnstile>\<^sub>p\<langle>Seq c1 c2,s\<rangle> \<Rightarrow> Stuck"
        by (auto intro: exec_Seq')
      with noabort have False
        by (auto simp add: final_notin_def)
      hence False ..
    }
    moreover 
    {
      assume "t \<in> Fault ` F"
      then obtain f where 
      t: "t=Fault f" and f: "f \<in> F"
        by auto
      from t exec_c1
      have "\<Gamma>\<turnstile>\<^sub>p\<langle>Seq c1 c2,s\<rangle> \<Rightarrow> Fault f"
        by (auto intro: exec_Seq')
      with noabort f have False
        by (auto simp add: final_notin_def)
      hence False ..
    }
    ultimately show False by auto
  qed
qed

lemma Seq_NoFaultStuckD2': 
  assumes noabort: "\<Gamma>\<turnstile>\<^sub>p\<langle>Seq c1 c2,s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault `  F)"
  shows "\<forall>t. \<Gamma>\<turnstile>\<^sub>p\<langle>c1,s\<rangle> \<Rightarrow> t \<longrightarrow> t\<notin> ({Stuck} \<union> Fault `  F) \<longrightarrow> 
             \<Gamma>\<turnstile>\<^sub>p\<langle>c2,t\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault `  F)"
using noabort
by (auto simp add: final_notin_def intro: exec_Seq') 


(* ************************************************************************* *)
subsection {* Lemmas about @{const "sequence"}, @{const "flatten"} and 
 @{const "normalize"} *}
(* ************************************************************************ *)

lemma execn_sequence_app: "\<And>s s' t.
 \<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq xs,Normal s\<rangle> =n\<Rightarrow> s'; \<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq ys,s'\<rangle> =n\<Rightarrow> t\<rbrakk>
 \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (xs@ys),Normal s\<rangle> =n\<Rightarrow> t"
proof (induct xs)
  case Nil 
  thus ?case by (auto elim: execn_Normal_elim_cases)
next
  case (Cons x xs)
  have exec_x_xs: "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (x # xs),Normal s\<rangle> =n\<Rightarrow> s'" by fact
  have exec_ys: "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq ys,s'\<rangle> =n\<Rightarrow> t" by fact
  show ?case
  proof (cases xs)
    case Nil
    with exec_x_xs have "\<Gamma>\<turnstile>\<^sub>p\<langle>x,Normal s\<rangle> =n\<Rightarrow> s'"
      by (auto elim: execn_Normal_elim_cases )
    with Nil exec_ys show ?thesis
      by (cases ys) (auto intro: execn.intros elim: execn_elim_cases)
  next
    case Cons
    with exec_x_xs
    obtain s'' where
      exec_x: "\<Gamma>\<turnstile>\<^sub>p\<langle>x,Normal s\<rangle> =n\<Rightarrow> s''" and
      exec_xs: "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq xs,s''\<rangle> =n\<Rightarrow> s'"
      by (auto elim: execn_Normal_elim_cases )
    show ?thesis
    proof (cases s'')
      case (Normal s''')
      from Cons.hyps [OF exec_xs [simplified Normal] exec_ys]
      have "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (xs @ ys),Normal s'''\<rangle> =n\<Rightarrow> t" .
      with Cons exec_x Normal
      show ?thesis
        by (auto intro: execn.intros)
    next
      case (Abrupt s''')
      with exec_xs have "s'=Abrupt s'''"
        by (auto dest: execn_Abrupt_end)
      with exec_ys have "t=Abrupt s'''"
        by (auto dest: execn_Abrupt_end)
      with exec_x Abrupt Cons show ?thesis
        by (auto intro: execn.intros)
    next
      case (Fault f)
      with exec_xs have "s'=Fault f"
        by (auto dest: execn_Fault_end)
      with exec_ys have "t=Fault f"
        by (auto dest: execn_Fault_end)
      with exec_x Fault Cons show ?thesis
        by (auto intro: execn.intros)
    next
      case Stuck
      with exec_xs have "s'=Stuck"
        by (auto dest: execn_Stuck_end)
      with exec_ys have "t=Stuck"
        by (auto dest: execn_Stuck_end)
      with exec_x Stuck Cons show ?thesis
        by (auto intro: execn.intros)
    qed
  qed
qed

lemma execn_sequence_appD: "\<And>s t. \<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (xs @ ys),Normal s\<rangle> =n\<Rightarrow> t \<Longrightarrow>
         \<exists>s'. \<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq xs,Normal s\<rangle> =n\<Rightarrow> s' \<and> \<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq ys,s'\<rangle> =n\<Rightarrow> t"
proof (induct xs)
  case Nil
  thus ?case
    by (auto intro: execn.intros)
next
  case (Cons x xs)
  have exec_app: "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq ((x # xs) @ ys),Normal s\<rangle> =n\<Rightarrow> t" by fact
  show ?case
  proof (cases xs)
    case Nil
    with exec_app show ?thesis
      by (cases ys) (auto elim: execn_Normal_elim_cases intro: execn_Skip')
  next
    case Cons
    with exec_app obtain s' where 
      exec_x: "\<Gamma>\<turnstile>\<^sub>p\<langle>x,Normal s\<rangle> =n\<Rightarrow> s'" and
      exec_xs_ys: "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (xs @ ys),s'\<rangle> =n\<Rightarrow> t"
      by (auto elim: execn_Normal_elim_cases)
    show ?thesis
    proof (cases s')
      case (Normal s'')
      from Cons.hyps [OF exec_xs_ys [simplified Normal]] Normal exec_x Cons
      show ?thesis
        by (auto intro: execn.intros)
    next
      case (Abrupt s'')
      with exec_xs_ys have "t=Abrupt s''"
        by (auto dest: execn_Abrupt_end)
      with Abrupt exec_x Cons
      show ?thesis
        by (auto intro: execn.intros)
    next
      case (Fault f)
      with exec_xs_ys have "t=Fault f"
        by (auto dest: execn_Fault_end)
      with Fault exec_x Cons
      show ?thesis
        by (auto intro: execn.intros)
    next
      case Stuck
      with exec_xs_ys have "t=Stuck"
        by (auto dest: execn_Stuck_end)
      with Stuck exec_x Cons
      show ?thesis
        by (auto intro: execn.intros)
    qed
  qed
qed
    
lemma execn_sequence_appE [consumes 1]: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (xs @ ys),Normal s\<rangle> =n\<Rightarrow> t;
   \<And>s'. \<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq xs,Normal s\<rangle> =n\<Rightarrow> s';\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq ys,s'\<rangle> =n\<Rightarrow> t\<rbrakk> \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  by (auto dest: execn_sequence_appD)

lemma execn_to_execn_sequence_flatten: 
  assumes exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"
  shows "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (flatten c),s\<rangle> =n\<Rightarrow> t"
using exec 
proof induct
  case (Seq c1 c2 n s s' s'') thus ?case 
    by (auto intro: execn.intros execn_sequence_app)
qed (auto intro: execn.intros)

lemma execn_to_execn_normalize: 
  assumes exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"
  shows "\<Gamma>\<turnstile>\<^sub>p\<langle>normalize c,s\<rangle> =n\<Rightarrow> t"
using exec 
proof induct
  case (Seq c1 c2 n s s' s'') thus ?case
    by (auto intro: execn_to_execn_sequence_flatten  execn_sequence_app )
next
  case (AwaitFalse s b c n) thus ?case using execn_to_execn_normalize
    by (simp add: execn.AwaitFalse)       
qed (auto intro: execn.intros execn_to_execn_normalize)



lemma execn_sequence_flatten_to_execn: 
  shows "\<And>s t. \<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (flatten c),s\<rangle> =n\<Rightarrow> t \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"
proof (induct c)
  case (Seq c1 c2)
  have exec_seq: "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (flatten (Seq c1 c2)),s\<rangle> =n\<Rightarrow> t" by fact
  show ?case
  proof (cases s)
    case (Normal s')
    with exec_seq obtain s'' where
      "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (flatten c1),Normal s'\<rangle> =n\<Rightarrow> s''" and
      "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (flatten c2),s''\<rangle> =n\<Rightarrow> t"
      by (auto elim: execn_sequence_appE)
    with Seq.hyps Normal
    show ?thesis
      by (fastforce intro: execn.intros)
  next
    case Abrupt 
    with exec_seq 
    show ?thesis by (auto intro: execn.intros dest: execn_Abrupt_end)
  next
    case Fault 
    with exec_seq 
    show ?thesis by (auto intro: execn.intros dest: execn_Fault_end)
  next
    case Stuck 
    with exec_seq 
    show ?thesis by (auto intro: execn.intros dest: execn_Stuck_end)
  qed
qed auto


lemma execn_normalize_to_execn: 
  shows "\<And>s t n. \<Gamma>\<turnstile>\<^sub>p\<langle>normalize c,s\<rangle> =n\<Rightarrow> t \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"
proof (induct c)
  case Skip thus ?case by simp
next
  case Basic thus ?case by simp
next
  case Spec thus ?case by simp
next
  case (Seq c1 c2)
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>normalize (Seq c1 c2),s\<rangle> =n\<Rightarrow> t" by fact
  hence exec_norm_seq: 
    "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (flatten (normalize c1) @ flatten (normalize c2)),s\<rangle> =n\<Rightarrow> t"
    by simp
  show ?case
  proof (cases s)
    case (Normal s')
    with exec_norm_seq obtain s'' where
      exec_norm_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (flatten (normalize c1)),Normal s'\<rangle> =n\<Rightarrow> s''" and
      exec_norm_c2: "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (flatten (normalize c2)),s''\<rangle> =n\<Rightarrow> t"
      by (auto elim: execn_sequence_appE)
    from execn_sequence_flatten_to_execn [OF exec_norm_c1]
      execn_sequence_flatten_to_execn [OF exec_norm_c2] Seq.hyps Normal
    show ?thesis
      by (fastforce intro: execn.intros)
  next
    case (Abrupt s')
    with exec_norm_seq have "t=Abrupt s'"
      by (auto dest: execn_Abrupt_end)
    with Abrupt show ?thesis
      by (auto intro: execn.intros)
  next
    case (Fault f)
    with exec_norm_seq have "t=Fault f"
      by (auto dest: execn_Fault_end)
    with Fault show ?thesis
      by (auto intro: execn.intros)
  next
    case Stuck
    with exec_norm_seq have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with Stuck show ?thesis
      by (auto intro: execn.intros)
  qed
next
  case Cond thus ?case
    by (auto intro: execn.intros elim!: execn_elim_cases)
next
  case (While b c)
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>normalize (While b c),s\<rangle> =n\<Rightarrow> t" by fact
  hence exec_norm_w: "\<Gamma>\<turnstile>\<^sub>p\<langle>While b (normalize c),s\<rangle> =n\<Rightarrow> t"
    by simp
  {
    fix s t w 
    assume exec_w: "\<Gamma>\<turnstile>\<^sub>p\<langle>w,s\<rangle> =n\<Rightarrow> t"
    have "w=While b (normalize c) \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>While b c,s\<rangle> =n\<Rightarrow> t"
      using exec_w 
    proof (induct)
      case (WhileTrue s b' c' n w t)
      from WhileTrue obtain 
        s_in_b: "s \<in> b" and
        exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>normalize c,Normal s\<rangle> =n\<Rightarrow> w" and
        hyp_w: "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,w\<rangle> =n\<Rightarrow> t"
        by simp
      from While.hyps [OF exec_c]
      have "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> w"
        by simp
      with hyp_w s_in_b
      have "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,Normal s\<rangle> =n\<Rightarrow> t"
        by (auto intro: execn.intros)
      with WhileTrue show ?case by simp
    qed (auto intro: execn.intros)
  }
  from this [OF exec_norm_w]
  show ?case
    by simp
next
  case Call thus ?case by simp
next
  case DynCom thus ?case by (auto intro: execn.intros elim!: execn_elim_cases)
next
  case Guard thus ?case by (auto intro: execn.intros elim!: execn_elim_cases)
next
  case Throw thus ?case by simp
next
  case Catch thus ?case by (fastforce intro: execn.intros elim!: execn_elim_cases)
next
  case (Await b c e)
  have normalized: "\<Gamma>\<turnstile>\<^sub>p\<langle>normalize (Await b c e),s\<rangle> =n\<Rightarrow> t" by fact
  hence exec_norm_a: "\<Gamma>\<turnstile>\<^sub>p\<langle>Await b (Language.normalize c) e,s\<rangle> =n\<Rightarrow> t" 
    by simp
  {
    fix s t a
    assume exec_a: "\<Gamma>\<turnstile>\<^sub>p\<langle>a,s\<rangle> =n\<Rightarrow> t"
    have "a=Await b (Language.normalize c) e \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>Await b c e,s\<rangle> =n\<Rightarrow> t"
      using exec_a 
    proof (induct)
      case (AwaitTrue s b' \<Gamma>1 c' n t)
      from AwaitTrue execn_normalize_to_execn obtain 
        s_in_b: "s \<in> b" and
        exec_c: "\<Gamma>1\<turnstile>\<langle>Language.normalize c,Normal s\<rangle> =n\<Rightarrow> t" and
        hyp_a: "\<Gamma>\<turnstile>\<^sub>p\<langle>Await b c e,Normal s\<rangle> =n\<Rightarrow> t" 
        using execn.AwaitTrue by fastforce              
      with hyp_a s_in_b
      have "\<Gamma>\<turnstile>\<^sub>p\<langle>Await b c e,Normal s\<rangle> =n\<Rightarrow> t"
        by (auto intro: execn.intros)
      with AwaitTrue show ?case by simp
    next
      case (AwaitFalse) thus ?case using execn.AwaitFalse by fastforce              
    qed (auto intro: execn.intros elim:execn_normalize_to_execn)
  }
  from this [OF exec_norm_a]
  show ?case
    by simp  
qed



lemma execn_normalize_iff_execn:
 "\<Gamma>\<turnstile>\<^sub>p\<langle>normalize c,s\<rangle> =n\<Rightarrow> t = \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" 
  by (auto intro: execn_to_execn_normalize execn_normalize_to_execn)

lemma exec_sequence_app: 
  assumes exec_xs: "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq xs,Normal s\<rangle> \<Rightarrow> s'" 
  assumes exec_ys: "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq ys,s'\<rangle> \<Rightarrow> t"
  shows "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (xs@ys),Normal s\<rangle> \<Rightarrow> t"
proof -
  from exec_to_execn [OF exec_xs]
  obtain n where 
    execn_xs: "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq xs,Normal s\<rangle> =n\<Rightarrow> s'"..
  from exec_to_execn [OF exec_ys]
  obtain m where
    execn_ys: "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq ys,s'\<rangle> =m\<Rightarrow> t"..
  with execn_xs obtain
    "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq xs,Normal s\<rangle> =max n m\<Rightarrow> s'"
    "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq ys,s'\<rangle> =max n m\<Rightarrow> t"
    by (auto intro: execn_mono max.cobounded1 max.cobounded2)
  from execn_sequence_app [OF this]
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (xs @ ys),Normal s\<rangle> =max n m\<Rightarrow> t" .
  thus ?thesis
    by (rule execn_to_exec)
qed

lemma exec_sequence_appD: 
  assumes exec_xs_ys: "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (xs @ ys),Normal s\<rangle> \<Rightarrow> t"
  shows "\<exists>s'. \<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq xs,Normal s\<rangle> \<Rightarrow> s' \<and> \<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq ys,s'\<rangle> \<Rightarrow> t"
proof -
  from exec_to_execn [OF exec_xs_ys]
  obtain n where "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (xs @ ys),Normal s\<rangle> =n\<Rightarrow> t"..
  thus ?thesis
    by (cases rule: execn_sequence_appE) (auto intro: execn_to_exec)
qed


lemma exec_sequence_appE [consumes 1]: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (xs @ ys),Normal s\<rangle> \<Rightarrow> t;
   \<And>s'. \<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq xs,Normal s\<rangle> \<Rightarrow> s';\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq ys,s'\<rangle> \<Rightarrow> t\<rbrakk> \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  by (auto dest: exec_sequence_appD)

lemma exec_to_exec_sequence_flatten: 
  assumes exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t"
  shows "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (flatten c),s\<rangle> \<Rightarrow> t"
proof -
  from exec_to_execn [OF exec]
  obtain n where "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"..
  from execn_to_execn_sequence_flatten [OF this]
  show ?thesis
    by (rule execn_to_exec)
qed

lemma exec_sequence_flatten_to_exec: 
  assumes exec_seq: "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (flatten c),s\<rangle> \<Rightarrow> t" 
  shows "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t"
proof -
  from exec_to_execn [OF exec_seq]
  obtain n where "\<Gamma>\<turnstile>\<^sub>p\<langle>sequence Seq (flatten c),s\<rangle> =n\<Rightarrow> t"..
  from execn_sequence_flatten_to_execn [OF this]
  show ?thesis
    by (rule execn_to_exec)
qed

lemma exec_to_exec_normalize: 
  assumes exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t"
  shows "\<Gamma>\<turnstile>\<^sub>p\<langle>normalize c,s\<rangle> \<Rightarrow> t"
proof -
  from exec_to_execn [OF exec] obtain n where "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"..
  hence "\<Gamma>\<turnstile>\<^sub>p\<langle>normalize c,s\<rangle> =n\<Rightarrow> t"
    by (rule execn_to_execn_normalize)
  thus ?thesis
    by (rule execn_to_exec)
qed

lemma exec_normalize_to_exec: 
  assumes exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>normalize c,s\<rangle> \<Rightarrow> t" 
  shows "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t"
proof -
  from exec_to_execn [OF exec] obtain n where "\<Gamma>\<turnstile>\<^sub>p\<langle>normalize c,s\<rangle> =n\<Rightarrow> t"..
  hence "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"
    by (rule execn_normalize_to_execn)
  thus ?thesis
    by (rule execn_to_exec)
qed

lemma exec_normalize_iff_exec:
 "\<Gamma>\<turnstile>\<^sub>p\<langle>normalize c,s\<rangle> \<Rightarrow> t = \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t" 
  by (auto intro: exec_to_exec_normalize exec_normalize_to_exec)
    
(* ************************************************************************* *)
subsection {* Lemmas about @{term "c\<^sub>1 \<subseteq>\<^sub>g c\<^sub>2"} *}
(* ************************************************************************ *)

lemma execn_to_execn_subseteq_guards: "\<And>c s t n. \<lbrakk>c \<subseteq>\<^sub>g\<^sub>s c'; \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t\<rbrakk>
    \<Longrightarrow> \<exists>t'. \<Gamma>\<turnstile>\<^sub>p\<langle>c',s\<rangle> =n\<Rightarrow> t' \<and> 
            (isFault t \<longrightarrow> isFault t') \<and> (\<not> isFault t' \<longrightarrow> t'=t)"
proof (induct c')
  case Skip thus ?case 
    by (fastforce dest: subseteq_guardsD elim: execn_elim_cases)
next
  case Basic thus ?case 
    by (fastforce dest: subseteq_guardsD elim: execn_elim_cases)
next
  case Spec thus ?case 
    by (fastforce dest: subseteq_guardsD elim: execn_elim_cases)
next
  case (Seq c1' c2')
  have "c \<subseteq>\<^sub>g\<^sub>s Seq c1' c2'" by fact
  from subseteq_guards_Seq [OF this]
  obtain c1 c2 where 
    c: "c = Seq c1 c2" and
    c1_c1': "c1 \<subseteq>\<^sub>g\<^sub>s c1'" and
    c2_c2': "c2 \<subseteq>\<^sub>g\<^sub>s c2'"
    by blast
  have exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" by fact
  with c obtain w where
    exec_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,s\<rangle> =n\<Rightarrow> w" and
    exec_c2: "\<Gamma>\<turnstile>\<^sub>p\<langle>c2,w\<rangle> =n\<Rightarrow> t"
    by (auto elim: execn_elim_cases)
  from exec_c1 Seq.hyps c1_c1'
  obtain w' where
    exec_c1': "\<Gamma>\<turnstile>\<^sub>p\<langle>c1',s\<rangle> =n\<Rightarrow> w'" and
    w_Fault: "isFault w \<longrightarrow> isFault w'" and
    w'_noFault: "\<not> isFault w' \<longrightarrow> w'=w"
    by blast
  show ?case
  proof (cases "s")
    case (Fault f)
    with exec have "t=Fault f"
      by (auto dest: execn_Fault_end)
    with Fault show ?thesis
      by auto
  next
    case Stuck
    with exec have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with Stuck show ?thesis
      by auto
  next
    case (Abrupt s')
    with exec have "t=Abrupt s'"
      by (auto dest: execn_Abrupt_end)
    with Abrupt show ?thesis
      by auto
  next
    case (Normal s')
    show ?thesis
    proof (cases "isFault w")
      case True
      then obtain f where w': "w=Fault f"..
      moreover with exec_c2 
      have t: "t=Fault f"
        by (auto dest: execn_Fault_end)
      ultimately show ?thesis
        using Normal w_Fault exec_c1'
        by (fastforce intro: execn.intros elim: isFaultE)      
    next
      case False
      note noFault_w = this
      show ?thesis
      proof (cases "isFault w'")
        case True
        then obtain f' where w': "w'=Fault f'"..
        with Normal exec_c1' 
        have exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>Seq c1' c2',s\<rangle> =n\<Rightarrow> Fault f'"
          by (auto intro: execn.intros)
        then show ?thesis
          by auto
      next
        case False
        with w'_noFault have w': "w'=w" by simp
        from Seq.hyps exec_c2 c2_c2'
        obtain t' where
          "\<Gamma>\<turnstile>\<^sub>p\<langle>c2',w\<rangle> =n\<Rightarrow> t'" and
          "isFault t \<longrightarrow> isFault t'" and
          "\<not> isFault t' \<longrightarrow> t'=t"
          by blast
        with Normal exec_c1' w'
        show ?thesis
          by (fastforce intro: execn.intros)
      qed
    qed
  qed
next
  case (Cond b c1' c2') 
  have exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" by fact
  have "c \<subseteq>\<^sub>g\<^sub>s Cond b c1' c2'" by fact
  from subseteq_guards_Cond [OF this]
  obtain c1 c2 where
    c: "c = Cond b c1 c2" and
    c1_c1': "c1 \<subseteq>\<^sub>g\<^sub>s c1'" and
    c2_c2': "c2 \<subseteq>\<^sub>g\<^sub>s c2'"
    by blast
  show ?case
  proof (cases "s")
    case (Fault f)
    with exec have "t=Fault f"
      by (auto dest: execn_Fault_end)
    with Fault show ?thesis
      by auto
  next
    case Stuck
    with exec have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with Stuck show ?thesis
      by auto
  next
    case (Abrupt s')
    with exec have "t=Abrupt s'"
      by (auto dest: execn_Abrupt_end)
    with Abrupt show ?thesis
      by auto
  next
    case (Normal s')
    from exec [simplified c Normal]
    show ?thesis
    proof (cases)
      assume s'_in_b: "s' \<in> b" 
      assume "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s'\<rangle> =n\<Rightarrow> t"
      with c1_c1' Normal Cond.hyps obtain t' where
        "\<Gamma>\<turnstile>\<^sub>p\<langle>c1',Normal s'\<rangle> =n\<Rightarrow> t'" 
        "isFault t \<longrightarrow> isFault t'" 
        "\<not> isFault t' \<longrightarrow> t' = t"
        by blast
      with s'_in_b Normal show ?thesis
        by (fastforce intro: execn.intros)
    next
      assume s'_notin_b: "s' \<notin> b" 
      assume "\<Gamma>\<turnstile>\<^sub>p\<langle>c2,Normal s'\<rangle> =n\<Rightarrow> t"
      with c2_c2' Normal Cond.hyps obtain t' where
        "\<Gamma>\<turnstile>\<^sub>p\<langle>c2',Normal s'\<rangle> =n\<Rightarrow> t'" 
        "isFault t \<longrightarrow> isFault t'" 
        "\<not> isFault t' \<longrightarrow> t' = t"
        by blast
      with s'_notin_b Normal show ?thesis
        by (fastforce intro: execn.intros)
    qed
  qed
next
  case (While b c')
  have exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" by fact
  have "c \<subseteq>\<^sub>g\<^sub>s While b c'" by fact
  from subseteq_guards_While [OF this]
  obtain c'' where 
    c: "c = While b c''" and
    c''_c': "c'' \<subseteq>\<^sub>g\<^sub>s c'"
    by blast
  {
    fix c r w
    assume exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,r\<rangle> =n\<Rightarrow> w"
    assume c: "c=While b c''"
    have "\<exists>w'. \<Gamma>\<turnstile>\<^sub>p\<langle>While b c',r\<rangle> =n\<Rightarrow> w' \<and>
                 (isFault w \<longrightarrow> isFault w') \<and> (\<not> isFault w' \<longrightarrow> w'=w)"
    using exec c
    proof (induct)
      case (WhileTrue r b' ca n u w)
      have eqs: "While b' ca = While b c''" by fact
      from WhileTrue have r_in_b: "r \<in> b" by simp
      from WhileTrue have exec_c'': "\<Gamma>\<turnstile>\<^sub>p\<langle>c'',Normal r\<rangle> =n\<Rightarrow> u" by simp
      from While.hyps [OF c''_c' exec_c''] obtain u' where
        exec_c': "\<Gamma>\<turnstile>\<^sub>p\<langle>c',Normal r\<rangle> =n\<Rightarrow> u'" and
        u_Fault: "isFault u \<longrightarrow> isFault u' "and 
        u'_noFault: "\<not> isFault u' \<longrightarrow> u' = u"
        by blast
      from WhileTrue obtain w' where
        exec_w: "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c',u\<rangle> =n\<Rightarrow> w'" and
        w_Fault: "isFault w \<longrightarrow> isFault w'" and
        w'_noFault: "\<not> isFault w' \<longrightarrow> w' = w"
        by blast
      show ?case
      proof (cases "isFault u'")
        case True
        with exec_c' r_in_b
        show ?thesis
          by (fastforce intro: execn.intros elim: isFaultE)
      next
        case False
        with exec_c' r_in_b u'_noFault exec_w w_Fault w'_noFault
        show ?thesis
          by (fastforce intro: execn.intros)
      qed
    next
      case WhileFalse thus ?case by (fastforce intro: execn.intros)
    qed auto
  }
  from this [OF exec c]
  show ?case .
next
  case Call thus ?case 
    by (fastforce dest: subseteq_guardsD elim: execn_elim_cases)
next
  case (DynCom C') 
  have exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" by fact
  have "c \<subseteq>\<^sub>g\<^sub>s DynCom C'" by fact
  from subseteq_guards_DynCom [OF this] obtain C where
    c: "c = DynCom C" and
    C_C': "\<forall>s. C s \<subseteq>\<^sub>g\<^sub>s C' s"
    by blast
  show ?case
  proof (cases "s")
    case (Fault f)
    with exec have "t=Fault f"
      by (auto dest: execn_Fault_end)
    with Fault show ?thesis
      by auto
  next
    case Stuck
    with exec have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with Stuck show ?thesis
      by auto
  next
    case (Abrupt s')
    with exec have "t=Abrupt s'"
      by (auto dest: execn_Abrupt_end)
    with Abrupt show ?thesis
      by auto
  next
    case (Normal s')
    from exec [simplified c Normal] 
    have "\<Gamma>\<turnstile>\<^sub>p\<langle>C s',Normal s'\<rangle> =n\<Rightarrow> t"
      by cases
    from DynCom.hyps C_C' [rule_format] this obtain t' where
      "\<Gamma>\<turnstile>\<^sub>p\<langle>C' s',Normal s'\<rangle> =n\<Rightarrow> t'"
      "isFault t \<longrightarrow> isFault t'" 
      "\<not> isFault t' \<longrightarrow> t' = t"
      by blast
    with Normal show ?thesis
      by (fastforce intro: execn.intros)
  qed
next
  case (Guard f' g' c')
  have exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" by fact
  have "c \<subseteq>\<^sub>g\<^sub>s Guard f' g' c'" by fact
  hence subset_cases: "(c \<subseteq>\<^sub>g\<^sub>s c') \<or> (\<exists>c''. c = Guard f' g' c'' \<and> (c'' \<subseteq>\<^sub>g\<^sub>s c'))"
    by (rule subseteq_guards_Guard)
  show ?case
  proof (cases "s")
    case (Fault f)
    with exec have "t=Fault f"
      by (auto dest: execn_Fault_end)
    with Fault show ?thesis
      by auto
  next
    case Stuck
    with exec have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with Stuck show ?thesis
      by auto
  next
    case (Abrupt s')
    with exec have "t=Abrupt s'"
      by (auto dest: execn_Abrupt_end)
    with Abrupt show ?thesis
      by auto
  next
    case (Normal s')
    from subset_cases show ?thesis
    proof 
      assume c_c': "c \<subseteq>\<^sub>g\<^sub>s c'"
      from Guard.hyps [OF this exec] Normal obtain t' where
        exec_c': "\<Gamma>\<turnstile>\<^sub>p\<langle>c',Normal s'\<rangle> =n\<Rightarrow> t'" and
        t_Fault: "isFault t \<longrightarrow> isFault t'" and 
        t_noFault: "\<not> isFault t' \<longrightarrow> t' = t" 
        by blast
      with Normal
      show ?thesis
        by (cases "s' \<in> g'") (fastforce intro: execn.intros)+
    next
      assume "\<exists>c''. c = Guard f' g' c'' \<and> (c'' \<subseteq>\<^sub>g\<^sub>s c')"
      then obtain c'' where
        c: "c = Guard f' g' c''" and
        c''_c': "c'' \<subseteq>\<^sub>g\<^sub>s c'"
        by blast
      from c exec Normal
      have exec_Guard': "\<Gamma>\<turnstile>\<^sub>p\<langle>Guard f' g' c'',Normal s'\<rangle> =n\<Rightarrow> t"
        by simp
      thus ?thesis
      proof (cases)
        assume s'_in_g': "s' \<in> g'"
        assume exec_c'': "\<Gamma>\<turnstile>\<^sub>p\<langle>c'',Normal s'\<rangle> =n\<Rightarrow> t"
        from Guard.hyps [OF c''_c' exec_c'']  obtain t' where
          exec_c': "\<Gamma>\<turnstile>\<^sub>p\<langle>c',Normal s'\<rangle> =n\<Rightarrow> t'" and
          t_Fault: "isFault t \<longrightarrow> isFault t'" and 
          t_noFault: "\<not> isFault t' \<longrightarrow> t' = t" 
          by blast
        with Normal s'_in_g'
        show ?thesis
          by (fastforce intro: execn.intros)
      next
        assume "s' \<notin> g'" "t=Fault f'"
        with Normal show ?thesis
          by (fastforce intro: execn.intros)
      qed
    qed
  qed
next
  case Throw thus ?case 
    by (fastforce dest: subseteq_guardsD intro: execn.intros 
         elim: execn_elim_cases)
next
  case (Catch c1' c2')
  have "c \<subseteq>\<^sub>g\<^sub>s Catch c1' c2'" by fact
  from subseteq_guards_Catch [OF this]
  obtain c1 c2 where 
    c: "c = Catch c1 c2" and
    c1_c1': "c1 \<subseteq>\<^sub>g\<^sub>s c1'" and
    c2_c2': "c2 \<subseteq>\<^sub>g\<^sub>s c2'"
    by blast
  have exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" by fact
  show ?case
  proof (cases "s")
    case (Fault f)
    with exec have "t=Fault f"
      by (auto dest: execn_Fault_end)
    with Fault show ?thesis
      by auto
  next
    case Stuck
    with exec have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with Stuck show ?thesis
      by auto
  next
    case (Abrupt s')
    with exec have "t=Abrupt s'"
      by (auto dest: execn_Abrupt_end)
    with Abrupt show ?thesis
      by auto
  next
    case (Normal s')
    from exec [simplified c Normal]
    show ?thesis
    proof (cases)
      fix w
      assume exec_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s'\<rangle> =n\<Rightarrow> Abrupt w" 
      assume exec_c2: "\<Gamma>\<turnstile>\<^sub>p\<langle>c2,Normal w\<rangle> =n\<Rightarrow> t"
      from Normal exec_c1 c1_c1' Catch.hyps obtain w' where
        exec_c1': "\<Gamma>\<turnstile>\<^sub>p\<langle>c1',Normal s'\<rangle> =n\<Rightarrow> w'" and
        w'_noFault:  "\<not> isFault w' \<longrightarrow> w' = Abrupt w"
        by blast
      show ?thesis
      proof (cases "isFault w'")
        case True
        with exec_c1' Normal show ?thesis
          by (fastforce intro: execn.intros elim: isFaultE)
      next
        case False
        with w'_noFault have w': "w'=Abrupt w" by simp
        from Normal exec_c2 c2_c2' Catch.hyps obtain t' where
          "\<Gamma>\<turnstile>\<^sub>p\<langle>c2',Normal w\<rangle> =n\<Rightarrow> t'" 
          "isFault t \<longrightarrow> isFault t'" 
          "\<not> isFault t' \<longrightarrow> t' = t"
          by blast
        with exec_c1' w' Normal
        show ?thesis
          by (fastforce intro: execn.intros )
      qed
    next
      assume exec_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s'\<rangle> =n\<Rightarrow> t" 
      assume t: "\<not> isAbr t"
      from Normal exec_c1 c1_c1' Catch.hyps obtain t' where
        exec_c1': "\<Gamma>\<turnstile>\<^sub>p\<langle>c1',Normal s'\<rangle> =n\<Rightarrow> t'" and
        t_Fault: "isFault t \<longrightarrow> isFault t'" and
        t'_noFault: "\<not> isFault t' \<longrightarrow> t' = t"
        by blast
      show ?thesis
      proof (cases "isFault t'")
        case True
        with exec_c1' Normal show ?thesis
          by (fastforce intro: execn.intros elim: isFaultE)
      next
        case False
        with exec_c1' Normal t_Fault t'_noFault t
        show ?thesis
          by (fastforce intro: execn.intros)
      qed
    qed
  qed
next
  case (Await b c' e)  
  then obtain c'' where c_Await:"c=Await b c'' e \<and> (c'' \<subseteq>\<^sub>g c')" using subseteq_guards_Await by blast
  thus ?case
    proof (cases "s")
      case Abrupt thus ?thesis
        using Await.prems(2) SemanticCon.execn_Abrupt_end by fastforce
    next
      case Stuck thus ?thesis
        using Await.prems(2) SemanticCon.execn_Stuck_end by blast
    next
      case Fault thus ?thesis  by auto
    next
      case (Normal x) thus ?thesis
      proof (cases "x \<in> b") 
        case True  
          then obtain "\<Gamma>1" where "\<Gamma>1\<turnstile> \<langle>c'',s\<rangle> =n\<Rightarrow> t" using c_Await Await
            by (metis Normal SemanticCon.execn_Normal_elim_cases(11))   
          then obtain t' where "\<Gamma>1\<turnstile> \<langle>c',s\<rangle> =n\<Rightarrow> t' \<and>
               (Semantic.isFault t \<longrightarrow> Semantic.isFault t') \<and> (\<not> Semantic.isFault t' \<longrightarrow> t' = t)" 
          using Semantic.execn_to_execn_subseteq_guards c_Await by blast    
          thus ?thesis  using Await.prems(1) Await.prems(2)  c_Await True SemanticCon.execn_Normal_elim_cases(11) 
             by (metis Normal Semantic.isFaultE SemanticCon.isFault_simps(3) execn.AwaitTrue execn_to_execn_subseteq_guards)
      next
       case False
       then show  "\<exists>t'. \<Gamma>\<turnstile>\<^sub>p \<langle>Await b c' e,s\<rangle> =n\<Rightarrow> t' \<and>
        (SemanticCon.isFault t \<longrightarrow> SemanticCon.isFault t') \<and>
        (\<not> SemanticCon.isFault t' \<longrightarrow> t' = t)" using False execn_Normal_elim_cases(11)
          by (metis Await.prems(2) Normal c_Await execn.AwaitFalse)      
      qed                 
   qed
qed


lemma exec_to_exec_subseteq_guards: 
  assumes c_c': "c \<subseteq>\<^sub>g\<^sub>s c'" 
  assumes  exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t"
  shows "\<exists>t'. \<Gamma>\<turnstile>\<^sub>p\<langle>c',s\<rangle> \<Rightarrow> t' \<and> 
             (isFault t \<longrightarrow> isFault t') \<and> (\<not> isFault t' \<longrightarrow> t'=t)"
proof -
  from exec_to_execn [OF exec] obtain n where
    "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" ..
  from execn_to_execn_subseteq_guards [OF c_c' this]
  show ?thesis
    by (blast intro: execn_to_exec)
qed

  
(* ************************************************************************* *)
subsection {* Lemmas about @{const "merge_guards"} *}
(* ************************************************************************ *)


theorem execn_to_execn_merge_guards:
 assumes exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" 
 shows "\<Gamma>\<turnstile>\<^sub>p\<langle>merge_guards c,s\<rangle> =n\<Rightarrow> t "
using exec_c 
proof (induct) 
  case (Guard s g c n t f)
  have s_in_g: "s \<in> g"  by fact
  have exec_merge_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>merge_guards c,Normal s\<rangle> =n\<Rightarrow> t" by fact
  show ?case
  proof (cases "\<exists>f' g' c'. merge_guards c = Guard f' g' c'")
    case False
    with exec_merge_c s_in_g
    show ?thesis
      by (cases "merge_guards c") (auto intro: execn.intros simp add: Let_def)
  next
    case True
    then obtain f' g' c' where 
      merge_guards_c: "merge_guards c = Guard f' g' c'"
      by iprover
    show ?thesis
    proof (cases "f=f'")
      case False
      from exec_merge_c s_in_g merge_guards_c False show ?thesis
        by (auto intro: execn.intros simp add: Let_def)
    next
      case True
      from exec_merge_c s_in_g merge_guards_c True show ?thesis 
        by (fastforce intro: execn.intros elim: execn.cases)
    qed
  qed
next
  case (GuardFault s g f c n)
  have s_notin_g: "s \<notin> g"  by fact
  show ?case
  proof (cases "\<exists>f' g' c'. merge_guards c = Guard f' g' c'")
    case False
    with s_notin_g
    show ?thesis
      by (cases "merge_guards c") (auto intro: execn.intros simp add: Let_def)
  next
    case True
    then obtain f' g' c' where 
      merge_guards_c: "merge_guards c = Guard f' g' c'"
      by iprover
    show ?thesis
    proof (cases "f=f'")
      case False
      from s_notin_g merge_guards_c False show ?thesis
        by (auto intro: execn.intros simp add: Let_def)
    next
      case True
      from  s_notin_g merge_guards_c True show ?thesis 
        by (fastforce intro: execn.intros)
    qed
  qed
next 
  case (AwaitTrue s b \<Gamma>1 c n t)
  then have "\<Gamma>1\<turnstile> \<langle>Language.merge_guards c,Normal s\<rangle> =n\<Rightarrow> t"
    by (simp add: AwaitTrue.hyps(2) execn_to_execn_merge_guards)
  thus ?case
    by (simp add: AwaitTrue.hyps(1) AwaitTrue.hyps(2) execn.AwaitTrue)    
qed (fastforce intro: execn.intros)+ 
    

lemma execn_merge_guards_to_execn_Normal:
  "\<And>s n t. \<Gamma>\<turnstile>\<^sub>p\<langle>merge_guards c,Normal s\<rangle> =n\<Rightarrow> t \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" 
proof (induct c)
  case Skip thus ?case by auto
next
  case Basic thus ?case by auto
next
  case Spec thus ?case by auto
next
  case (Seq c1 c2) 
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>merge_guards (Seq c1 c2),Normal s\<rangle> =n\<Rightarrow> t" by fact
  hence exec_merge: "\<Gamma>\<turnstile>\<^sub>p\<langle>Seq (merge_guards c1) (merge_guards c2),Normal s\<rangle> =n\<Rightarrow> t"
    by simp
  then obtain s' where
    exec_merge_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>merge_guards c1,Normal s\<rangle> =n\<Rightarrow> s'" and
    exec_merge_c2: "\<Gamma>\<turnstile>\<^sub>p\<langle>merge_guards c2,s'\<rangle> =n\<Rightarrow> t"
    by cases
  from exec_merge_c1
  have exec_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> =n\<Rightarrow> s'"
    by (rule Seq.hyps)
  show ?case
  proof (cases s')
    case (Normal s'')
    with exec_merge_c2
    have "\<Gamma>\<turnstile>\<^sub>p\<langle>c2,s'\<rangle> =n\<Rightarrow> t"
      by (auto intro: Seq.hyps)
    with exec_c1 show ?thesis
      by (auto intro: execn.intros)
  next
    case (Abrupt s'')
    with exec_merge_c2 have "t=Abrupt s''"
      by (auto dest: execn_Abrupt_end)
    with exec_c1 Abrupt
    show ?thesis
      by (auto intro: execn.intros)
  next
    case (Fault f)
    with exec_merge_c2 have "t=Fault f"
      by (auto dest: execn_Fault_end)
    with exec_c1 Fault
    show ?thesis
      by (auto intro: execn.intros)
  next
    case Stuck
    with exec_merge_c2 have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with exec_c1 Stuck
    show ?thesis
      by (auto intro: execn.intros)
  qed
next
  case Cond thus ?case
    by (fastforce intro: execn.intros elim: execn_Normal_elim_cases)
next
  case (While b c) 
  {
    fix c' r w
    assume exec_c': "\<Gamma>\<turnstile>\<^sub>p\<langle>c',r\<rangle> =n\<Rightarrow> w"
    assume c': "c'=While b (merge_guards c)"
    have "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,r\<rangle> =n\<Rightarrow> w"
      using exec_c' c' 
    proof (induct)
      case (WhileTrue r b' c'' n u w)
      have eqs: "While b' c'' = While b (merge_guards c)" by fact
      from WhileTrue 
      have r_in_b: "r \<in> b" 
        by simp
      from WhileTrue While.hyps have exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal r\<rangle> =n\<Rightarrow> u"
        by simp
      from WhileTrue have exec_w: "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,u\<rangle> =n\<Rightarrow> w"
        by simp
      from r_in_b exec_c exec_w
      show ?case
        by (rule execn.WhileTrue)
    next
      case WhileFalse thus ?case by (auto intro: execn.WhileFalse)
    qed auto
  } 
  with While.prems show ?case
    by (auto)
next
  case Call thus ?case by simp
next
  case DynCom thus ?case
    by (fastforce intro: execn.intros elim: execn_Normal_elim_cases)
next
  case (Guard f g c)
  have exec_merge: "\<Gamma>\<turnstile>\<^sub>p\<langle>merge_guards (Guard f g c),Normal s\<rangle> =n\<Rightarrow> t" by fact
  show ?case
  proof (cases "s \<in> g")
    case False
    with exec_merge have "t=Fault f"
      by (auto split: com.splits if_split_asm elim: execn_Normal_elim_cases 
        simp add: Let_def is_Guard_def)
    with False show ?thesis
      by (auto intro: execn.intros)
  next
    case True
    note s_in_g = this
    show ?thesis
    proof (cases "\<exists>f' g' c'. merge_guards c = Guard f' g' c'")
      case False
      then
      have "merge_guards (Guard f g c) = Guard f g (merge_guards c)"
        by (cases "merge_guards c") (auto simp add: Let_def)
      with exec_merge s_in_g
      obtain "\<Gamma>\<turnstile>\<^sub>p\<langle>merge_guards c,Normal s\<rangle> =n\<Rightarrow> t"
        by (auto elim: execn_Normal_elim_cases)
      from Guard.hyps [OF this] s_in_g
      show ?thesis
        by (auto intro: execn.intros)
    next
      case True
      then obtain f' g' c' where 
        merge_guards_c: "merge_guards c = Guard f' g' c'"
        by iprover
      show ?thesis
      proof (cases "f=f'")
        case False
        with merge_guards_c
        have "merge_guards (Guard f g c) = Guard f g (merge_guards c)"
          by (simp add: Let_def)
        with exec_merge s_in_g
        obtain "\<Gamma>\<turnstile>\<^sub>p\<langle>merge_guards c,Normal s\<rangle> =n\<Rightarrow> t"
          by (auto elim: execn_Normal_elim_cases)
        from Guard.hyps [OF this] s_in_g
        show ?thesis
          by (auto intro: execn.intros)
      next
        case True
        note f_eq_f' = this
        with merge_guards_c have 
          merge_guards_Guard: "merge_guards (Guard f g c) = Guard f (g \<inter> g') c'"
          by simp
        show ?thesis
        proof (cases "s \<in> g'")
          case True
          with exec_merge merge_guards_Guard merge_guards_c s_in_g
          have "\<Gamma>\<turnstile>\<^sub>p\<langle>merge_guards c,Normal s\<rangle> =n\<Rightarrow> t"
            by (auto intro: execn.intros elim: execn_Normal_elim_cases)
          with Guard.hyps [OF this] s_in_g
          show ?thesis
            by (auto intro: execn.intros)
        next
          case False
          with exec_merge merge_guards_Guard 
          have "t=Fault f"
            by (auto elim: execn_Normal_elim_cases)
          with merge_guards_c f_eq_f' False
          have "\<Gamma>\<turnstile>\<^sub>p\<langle>merge_guards c,Normal s\<rangle> =n\<Rightarrow> t"
            by (auto intro: execn.intros)
          from Guard.hyps [OF this] s_in_g
          show ?thesis
            by (auto intro: execn.intros)
        qed
      qed
    qed
  qed
next
  case Throw thus ?case by simp
next
  case (Catch c1 c2)
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>merge_guards (Catch c1 c2),Normal s\<rangle> =n\<Rightarrow> t"  by fact
  hence "\<Gamma>\<turnstile>\<^sub>p\<langle>Catch (merge_guards c1) (merge_guards c2),Normal s\<rangle> =n\<Rightarrow> t" by simp
  thus ?case
    by cases (auto intro: execn.intros Catch.hyps)
next 
  case (Await b c e) 
  {
    fix c' r w
    assume exec_c': "\<Gamma>\<turnstile>\<^sub>p\<langle>c',r\<rangle> =n\<Rightarrow> w"
    assume c': "c'=Await b (Language.merge_guards c) e"
    have "\<Gamma>\<turnstile>\<^sub>p\<langle>Await b c e,r\<rangle> =n\<Rightarrow> w"
      using exec_c' c' 
    proof (induct)
      case (AwaitTrue r b' \<Gamma>1 c'' n u) 
      then have eqs: "Await b' c'' e = Await b (Language.merge_guards c) e" by auto
      from AwaitTrue 
      have r_in_b: "r \<in> b" 
        by simp
      from AwaitTrue have exec_c: "\<Gamma>1\<turnstile>\<langle>c,Normal r\<rangle> =n\<Rightarrow> u"
        using execn_merge_guards_to_execn by force  
      then have "\<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>c,Normal r\<rangle> =n\<Rightarrow> u"  using AwaitTrue.hyps(2) exec_c by blast      
      then have exec_a: "\<Gamma>\<turnstile>\<^sub>p\<langle>Await b c e,Normal r\<rangle> =n\<Rightarrow> u"
        by (meson exec_c execn.AwaitTrue r_in_b)       
      from r_in_b exec_c exec_a
      show ?case
        by (simp add: execn.AwaitTrue) 
    next
      case (AwaitFalse b c) thus ?case by (simp add: execn.AwaitFalse)  
    qed auto
  } 
  with Await.prems show ?case
    by (auto) 
qed
  
theorem execn_merge_guards_to_execn:
  "\<Gamma>\<turnstile>\<^sub>p\<langle>merge_guards c,s\<rangle> =n\<Rightarrow> t \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c, s\<rangle> =n\<Rightarrow> t" 
apply (cases s)
apply    (fastforce intro: execn_merge_guards_to_execn_Normal)
apply   (fastforce dest: execn_Abrupt_end)
apply  (fastforce dest: execn_Fault_end)
apply (fastforce dest: execn_Stuck_end)
done

corollary execn_iff_execn_merge_guards:
 "\<Gamma>\<turnstile>\<^sub>p\<langle>c, s\<rangle> =n\<Rightarrow> t = \<Gamma>\<turnstile>\<^sub>p\<langle>merge_guards c,s\<rangle> =n\<Rightarrow> t"
  by (blast intro: execn_merge_guards_to_execn execn_to_execn_merge_guards)

theorem exec_iff_exec_merge_guards:
 "\<Gamma>\<turnstile>\<^sub>p\<langle>c, s\<rangle> \<Rightarrow> t = \<Gamma>\<turnstile>\<^sub>p\<langle>merge_guards c,s\<rangle> \<Rightarrow> t"
  by (blast dest: exec_to_execn intro: execn_to_exec
            intro: execn_to_execn_merge_guards
                   execn_merge_guards_to_execn)

corollary exec_to_exec_merge_guards:
 "\<Gamma>\<turnstile>\<^sub>p\<langle>c, s\<rangle> \<Rightarrow> t \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>merge_guards c,s\<rangle> \<Rightarrow> t"
  by (rule iffD1 [OF exec_iff_exec_merge_guards])

corollary exec_merge_guards_to_exec:
 "\<Gamma>\<turnstile>\<^sub>p\<langle>merge_guards c,s\<rangle> \<Rightarrow> t \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c, s\<rangle> \<Rightarrow> t"
  by (rule iffD2 [OF exec_iff_exec_merge_guards])

(* ************************************************************************* *)
subsection {* Lemmas about @{const "mark_guards"} *}
(* ************************************************************************ *)

lemma execn_to_execn_mark_guards:
 assumes exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" 
 assumes t_not_Fault: "\<not> isFault t"
 shows "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards f c,s\<rangle> =n\<Rightarrow> t "
using exec_c t_not_Fault [simplified not_isFault_iff]
proof induct
 case (AwaitTrue s b \<Gamma>1 c n t)
 then have "\<Gamma>1\<turnstile> \<langle>Language.mark_guards f c,Normal s\<rangle> =n\<Rightarrow> t"
      by (meson Semantic.isFaultE execn_to_execn_mark_guards)
 thus ?case by (auto intro:AwaitTrue.hyps(1) AwaitTrue.hyps(2) execn.AwaitTrue)
qed(auto intro: execn.intros  dest: noFaultn_startD')

lemma execn_to_execn_mark_guards_Fault:
 assumes exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"
 shows "\<And>f. \<lbrakk>t=Fault f\<rbrakk> \<Longrightarrow> \<exists>f'. \<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards x c,s\<rangle> =n\<Rightarrow> Fault f'"
using exec_c 
proof (induct)
  case Skip thus ?case by auto
next
  case Guard thus ?case by (fastforce intro: execn.intros)
next
  case GuardFault thus ?case by (fastforce intro: execn.intros)
next
  case FaultProp thus ?case by auto
next
 case Basic thus ?case by auto
next
 case Spec thus ?case by auto
next
 case SpecStuck thus ?case by auto
next
  case (Seq c1 s n w c2 t)
  have exec_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> =n\<Rightarrow> w" by fact
  have exec_c2: "\<Gamma>\<turnstile>\<^sub>p\<langle>c2,w\<rangle> =n\<Rightarrow> t" by fact
  have t: "t=Fault f" by fact
  show ?case
  proof (cases w)
    case (Fault f')
    with exec_c2 t have "f'=f"
      by (auto dest: execn_Fault_end)
    with Fault Seq.hyps obtain f'' where
      "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards x c1,Normal s\<rangle> =n\<Rightarrow> Fault f''"
      by auto
    moreover have "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards x c2,Fault f''\<rangle> =n\<Rightarrow> Fault f''"
      by auto
    ultimately show ?thesis
      by (auto intro: execn.intros)
  next
    case (Normal s')
    with execn_to_execn_mark_guards [OF exec_c1] 
    have exec_mark_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards x c1,Normal s\<rangle> =n\<Rightarrow> w"
      by simp
    with Seq.hyps t obtain f' where
      "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards x c2,w\<rangle> =n\<Rightarrow> Fault f'" 
      by blast
    with exec_mark_c1 show ?thesis
      by (auto intro: execn.intros)
  next
    case (Abrupt s')
    with execn_to_execn_mark_guards [OF exec_c1] 
    have exec_mark_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards x c1,Normal s\<rangle> =n\<Rightarrow> w"
      by simp
    with Seq.hyps t obtain f' where
      "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards x c2,w\<rangle> =n\<Rightarrow> Fault f'" 
      by (auto intro: execn.intros)
    with exec_mark_c1 show ?thesis
      by (auto intro: execn.intros)
  next
    case Stuck
    with exec_c2 have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with t show ?thesis by simp
  qed
next
  case CondTrue thus ?case by (fastforce intro: execn.intros)
next
  case CondFalse thus ?case by (fastforce intro: execn.intros)
next
  case (WhileTrue s b c n w t) 
  have exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> w" by fact
  have exec_w: "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,w\<rangle> =n\<Rightarrow> t" by fact
  have t: "t = Fault f" by fact
  have s_in_b: "s \<in> b" by fact
  show ?case
  proof (cases w)
    case (Fault f')
    with exec_w t have "f'=f"
      by (auto dest: execn_Fault_end)
    with Fault WhileTrue.hyps obtain f'' where
      "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards x c,Normal s\<rangle> =n\<Rightarrow> Fault f''"
      by auto
    moreover have "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards x (While b c),Fault f''\<rangle> =n\<Rightarrow> Fault f''"
      by auto
    ultimately show ?thesis
      using s_in_b by (auto intro: execn.intros)
  next
    case (Normal s')
    with execn_to_execn_mark_guards [OF exec_c] 
    have exec_mark_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards x c,Normal s\<rangle> =n\<Rightarrow> w"
      by simp
    with WhileTrue.hyps t obtain f' where
      "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards x (While b c),w\<rangle> =n\<Rightarrow> Fault f'" 
      by blast
    with exec_mark_c s_in_b show ?thesis
      by (auto intro: execn.intros)
  next
    case (Abrupt s')
    with execn_to_execn_mark_guards [OF exec_c] 
    have exec_mark_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards x c,Normal s\<rangle> =n\<Rightarrow> w"
      by simp
    with WhileTrue.hyps t obtain f' where
      "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards x (While b c),w\<rangle> =n\<Rightarrow> Fault f'" 
      by (auto intro: execn.intros)
    with exec_mark_c s_in_b show ?thesis
      by (auto intro: execn.intros)
  next
    case Stuck
    with exec_w have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with t show ?thesis by simp
  qed
next
  case WhileFalse thus ?case by (fastforce intro: execn.intros)
next
  case Call thus ?case by (fastforce intro: execn.intros)
next
  case CallUndefined thus ?case by simp
next
  case StuckProp thus ?case by simp
next
  case DynCom thus ?case by (fastforce intro: execn.intros)
next
  case Throw thus ?case by simp
next
  case AbruptProp thus ?case by simp
next
  case (CatchMatch c1 s n w c2 t) 
  have exec_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> =n\<Rightarrow> Abrupt w" by fact
  have exec_c2: "\<Gamma>\<turnstile>\<^sub>p\<langle>c2,Normal w\<rangle> =n\<Rightarrow> t" by fact
  have t: "t = Fault f" by fact
  from execn_to_execn_mark_guards [OF exec_c1]
  have exec_mark_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards x c1,Normal s\<rangle> =n\<Rightarrow> Abrupt w"
    by simp
  with CatchMatch.hyps t obtain f' where
    "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards x c2,Normal w\<rangle> =n\<Rightarrow> Fault f'" 
    by blast
  with exec_mark_c1 show ?case
    by (auto intro: execn.intros)
next
  case CatchMiss thus ?case by (fastforce intro: execn.intros)
next
  case (AwaitTrue s b \<Gamma>1 c n t)
  then have "\<exists>f'. \<Gamma>1\<turnstile>\<langle>Language.mark_guards x c,Normal s\<rangle> =n\<Rightarrow> Fault f'"
       by (simp add: execn_to_execn_mark_guards_Fault) 
  thus ?case using AwaitTrue.hyps(1) AwaitTrue.hyps(2) execn.AwaitTrue by fastforce 
next
  case (AwaitFalse s b) thus ?case by (auto simp add:execn.AwaitFalse)
qed

lemma execn_mark_guards_to_execn:
  "\<And>s n t. \<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards f c,s\<rangle> =n\<Rightarrow> t
  \<Longrightarrow> \<exists>t'. \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t' \<and> 
            (isFault t \<longrightarrow> isFault t') \<and> 
            (t' = Fault f \<longrightarrow> t'=t) \<and>
            (isFault t' \<longrightarrow> isFault t) \<and>
            (\<not> isFault t' \<longrightarrow> t'=t)"
proof (induct c)
  case Skip thus ?case by auto
next
  case Basic thus ?case by auto
next
  case Spec thus ?case by auto
next
  case (Seq c1 c2 s n t)
  have exec_mark: "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards f (Seq c1 c2),s\<rangle> =n\<Rightarrow> t" by fact
  then obtain w where 
    exec_mark_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards f c1,s\<rangle> =n\<Rightarrow> w" and
    exec_mark_c2: "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards f c2,w\<rangle> =n\<Rightarrow> t"
    by (auto elim: execn_elim_cases)
  from Seq.hyps exec_mark_c1
  obtain w' where 
    exec_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,s\<rangle> =n\<Rightarrow> w'" and
    w_Fault: "isFault w \<longrightarrow> isFault w'" and
    w'_Fault_f: "w' = Fault f \<longrightarrow> w'=w" and
    w'_Fault: "isFault w' \<longrightarrow> isFault w" and
    w'_noFault: "\<not> isFault w' \<longrightarrow> w'=w"
    by blast
  show ?case
  proof (cases "s")
    case (Fault f)
    with exec_mark have "t=Fault f"
      by (auto dest: execn_Fault_end)
    with Fault show ?thesis
      by auto
  next
    case Stuck
    with exec_mark have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with Stuck show ?thesis
      by auto
  next
    case (Abrupt s')
    with exec_mark have "t=Abrupt s'"
      by (auto dest: execn_Abrupt_end)
    with Abrupt show ?thesis
      by auto
  next
    case (Normal s')
    show ?thesis
    proof (cases "isFault w")
      case True
      then obtain f where w': "w=Fault f"..
      moreover with exec_mark_c2 
      have t: "t=Fault f"
        by (auto dest: execn_Fault_end)
      ultimately show ?thesis
        using Normal w_Fault w'_Fault_f exec_c1
        by (fastforce intro: execn.intros elim: isFaultE)      
    next
      case False
      note noFault_w = this
      show ?thesis
      proof (cases "isFault w'")
        case True
        then obtain f' where w': "w'=Fault f'"..
        with Normal exec_c1 
        have exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>Seq c1 c2,s\<rangle> =n\<Rightarrow> Fault f'"
          by (auto intro: execn.intros)
        from w'_Fault_f w' noFault_w
        have "f' \<noteq> f"
          by (cases w) auto
        moreover
        from w' w'_Fault exec_mark_c2 have "isFault t" 
          by (auto dest: execn_Fault_end elim: isFaultE)
        ultimately 
        show ?thesis
          using exec
          by auto
      next
        case False
        with w'_noFault have w': "w'=w" by simp
        from Seq.hyps exec_mark_c2
        obtain t' where
          "\<Gamma>\<turnstile>\<^sub>p\<langle>c2,w\<rangle> =n\<Rightarrow> t'" and
          "isFault t \<longrightarrow> isFault t'" and
          "t' = Fault f \<longrightarrow> t'=t" and
          "isFault t' \<longrightarrow> isFault t" and
          "\<not> isFault t' \<longrightarrow> t'=t"
          by blast
        with Normal exec_c1 w'
        show ?thesis
          by (fastforce intro: execn.intros)
      qed
    qed
  qed
next
  case (Cond b c1 c2 s n t)
  have exec_mark: "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards f (Cond b c1 c2),s\<rangle> =n\<Rightarrow> t" by fact
  show ?case
  proof (cases s)
    case (Fault f)
    with exec_mark have "t=Fault f"
      by (auto dest: execn_Fault_end)
    with Fault show ?thesis
      by auto
  next
    case Stuck
    with exec_mark have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with Stuck show ?thesis
      by auto
  next
    case (Abrupt s')
    with exec_mark have "t=Abrupt s'"
      by (auto dest: execn_Abrupt_end)
    with Abrupt show ?thesis
      by auto
  next
    case (Normal s')
    show ?thesis
    proof (cases "s'\<in> b")
      case True
      with Normal exec_mark
      have "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards f c1 ,Normal s'\<rangle> =n\<Rightarrow> t"
        by (auto elim: execn_Normal_elim_cases)
      with Normal True Cond.hyps obtain t'
        where "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s'\<rangle> =n\<Rightarrow> t'" 
            "isFault t \<longrightarrow> isFault t'" 
            "t' = Fault f \<longrightarrow> t'=t"
            "isFault t' \<longrightarrow> isFault t"
            "\<not> isFault t' \<longrightarrow> t' = t"
        by blast
      with Normal True
      show ?thesis
        by (blast intro: execn.intros)
    next
      case False
      with Normal exec_mark
      have "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards f c2 ,Normal s'\<rangle> =n\<Rightarrow> t"
        by (auto elim: execn_Normal_elim_cases)
      with Normal False Cond.hyps obtain t'
        where "\<Gamma>\<turnstile>\<^sub>p\<langle>c2,Normal s'\<rangle> =n\<Rightarrow> t'" 
            "isFault t  \<longrightarrow> isFault t'" 
            "t' = Fault f  \<longrightarrow> t'=t"
            "isFault t' \<longrightarrow> isFault t"
            "\<not> isFault t' \<longrightarrow> t' = t"
        by blast
      with Normal False
      show ?thesis
        by (blast intro: execn.intros)
    qed
  qed
next
  case (While b c s n t)
  have exec_mark: "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards f (While b c),s\<rangle> =n\<Rightarrow> t" by fact
  show ?case
  proof (cases s)
    case (Fault f)
    with exec_mark have "t=Fault f"
      by (auto dest: execn_Fault_end)
    with Fault show ?thesis
      by auto
  next
    case Stuck
    with exec_mark have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with Stuck show ?thesis
      by auto
  next
    case (Abrupt s')
    with exec_mark have "t=Abrupt s'"
      by (auto dest: execn_Abrupt_end)
    with Abrupt show ?thesis
      by auto
  next
    case (Normal s')
    {
      fix c' r w
      assume exec_c': "\<Gamma>\<turnstile>\<^sub>p\<langle>c',r\<rangle> =n\<Rightarrow> w"
      assume c': "c'=While b (mark_guards f c)"
      have "\<exists>w'. \<Gamma>\<turnstile>\<^sub>p\<langle>While b c,r\<rangle> =n\<Rightarrow> w' \<and> (isFault w \<longrightarrow> isFault w') \<and>
                   (w' = Fault f \<longrightarrow> w'=w) \<and> (isFault w' \<longrightarrow> isFault w) \<and>
                   (\<not> isFault w' \<longrightarrow> w'=w)"
        using exec_c' c' 
      proof (induct)
        case (WhileTrue r b' c'' n u w)
        have eqs: "While b' c'' = While b (mark_guards f c)" by fact
        from WhileTrue.hyps eqs
        have r_in_b: "r\<in>b" by simp
        from WhileTrue.hyps eqs
        have exec_mark_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards f c,Normal r\<rangle> =n\<Rightarrow> u" by simp
        from WhileTrue.hyps eqs
        have exec_mark_w: "\<Gamma>\<turnstile>\<^sub>p\<langle>While b (mark_guards f c),u\<rangle> =n\<Rightarrow> w"
          by simp
        show ?case
        proof -
          from WhileTrue.hyps eqs have "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards f c,Normal r\<rangle> =n\<Rightarrow> u"
            by simp
          with While.hyps
          obtain u' where 
            exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal r\<rangle> =n\<Rightarrow> u'" and
            u_Fault: "isFault u \<longrightarrow> isFault u'" and
            u'_Fault_f: "u' = Fault f \<longrightarrow> u'=u" and
            u'_Fault: "isFault u' \<longrightarrow> isFault u" and
            u'_noFault: "\<not> isFault u' \<longrightarrow> u'=u"
            by blast
          show ?thesis
          proof (cases "isFault u'")
            case False
            with u'_noFault have u': "u'=u" by simp
            from WhileTrue.hyps eqs obtain w' where
              "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,u\<rangle> =n\<Rightarrow> w'"
              "isFault w  \<longrightarrow> isFault w'"
              "w' = Fault f \<longrightarrow> w'=w" 
              "isFault w' \<longrightarrow> isFault w" 
              "\<not> isFault w' \<longrightarrow> w' = w"
              by blast
            with u' exec_c r_in_b 
            show ?thesis
              by (blast intro: execn.WhileTrue)
          next
            case True
            then obtain f' where u': "u'=Fault f'"..
            with exec_c r_in_b 
            have exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,Normal r\<rangle> =n\<Rightarrow> Fault f'"
              by (blast intro: execn.intros)
            from True u'_Fault have "isFault u"
              by simp
            then obtain f where u: "u=Fault f"..
            with exec_mark_w have "w=Fault f"
              by (auto dest: execn_Fault_end)
            with exec u' u u'_Fault_f
            show ?thesis
              by auto
          qed
        qed
      next
        case (WhileFalse r b' c'' n)
        have eqs: "While b'  c'' = While b (mark_guards f c)" by fact
        from WhileFalse.hyps eqs
        have r_not_in_b: "r\<notin>b" by simp
        show ?case
        proof -
          from r_not_in_b 
          have "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,Normal r\<rangle> =n\<Rightarrow> Normal r"
            by (rule execn.WhileFalse)
          thus ?thesis
            by blast
        qed
      qed auto
    } note hyp_while = this
    show ?thesis
    proof (cases "s'\<in>b") 
      case False
      with Normal exec_mark
      have "t=s"
        by (auto elim: execn_Normal_elim_cases)
      with Normal False show ?thesis
        by (auto intro: execn.intros)
    next
      case True note s'_in_b = this
      with Normal exec_mark obtain r where
        exec_mark_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards f c,Normal s'\<rangle> =n\<Rightarrow> r" and
        exec_mark_w: "\<Gamma>\<turnstile>\<^sub>p\<langle>While b (mark_guards f c),r\<rangle> =n\<Rightarrow> t"
        by (auto elim: execn_Normal_elim_cases)
      from While.hyps exec_mark_c obtain r' where 
        exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s'\<rangle> =n\<Rightarrow> r'" and
        r_Fault: "isFault r \<longrightarrow> isFault r'" and
        r'_Fault_f: "r' = Fault f \<longrightarrow> r'=r" and
        r'_Fault: "isFault r' \<longrightarrow> isFault r" and
        r'_noFault: "\<not> isFault r' \<longrightarrow> r'=r"
        by blast
      show ?thesis
      proof (cases "isFault r'")
        case False
        with r'_noFault have r': "r'=r" by simp
        from hyp_while exec_mark_w 
        obtain t' where
          "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,r\<rangle> =n\<Rightarrow> t'"
          "isFault t \<longrightarrow> isFault t'"
          "t' = Fault f \<longrightarrow> t'=t"
          "isFault t' \<longrightarrow> isFault t"
          "\<not> isFault t' \<longrightarrow> t'=t"
          by blast
        with r' exec_c Normal s'_in_b
        show ?thesis
          by (blast intro: execn.intros)
      next
        case True
        then obtain f' where r': "r'=Fault f'"..
        hence "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,r'\<rangle> =n\<Rightarrow> Fault f'"
          by auto 
        with Normal s'_in_b exec_c
        have exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,Normal s'\<rangle> =n\<Rightarrow> Fault f'"
          by (auto intro: execn.intros)
        from True r'_Fault
        have "isFault r"
          by simp
        then obtain f where r: "r=Fault f"..
        with exec_mark_w have "t=Fault f"
          by (auto dest: execn_Fault_end)
        with Normal exec r' r r'_Fault_f
        show ?thesis
          by auto
      qed
    qed
  qed
next
  case Call thus ?case by auto
next
  case DynCom thus ?case 
    by (fastforce elim!: execn_elim_cases intro: execn.intros)
next
  case (Guard f' g c s n t)
  have exec_mark: "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards f (Guard f' g c),s\<rangle> =n\<Rightarrow> t" by fact
  show ?case
  proof (cases s)
    case (Fault f)
    with exec_mark have "t=Fault f"
      by (auto dest: execn_Fault_end)
    with Fault show ?thesis
      by auto
  next
    case Stuck
    with exec_mark have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with Stuck show ?thesis
      by auto
  next
    case (Abrupt s')
    with exec_mark have "t=Abrupt s'"
      by (auto dest: execn_Abrupt_end)
    with Abrupt show ?thesis
      by auto
  next
    case (Normal s')
    show ?thesis
    proof (cases "s'\<in>g")
      case False
      with Normal exec_mark have t: "t=Fault f"
        by (auto elim: execn_Normal_elim_cases)
      from False
      have "\<Gamma>\<turnstile>\<^sub>p\<langle>Guard f' g c,Normal s'\<rangle> =n\<Rightarrow> Fault f'"
        by (blast intro: execn.intros)
      with Normal t show ?thesis
        by auto
    next
      case True
      with exec_mark Normal 
      have "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards f c,Normal s'\<rangle> =n\<Rightarrow> t"
        by (auto elim: execn_Normal_elim_cases)
      with Guard.hyps obtain t' where
        "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s'\<rangle> =n\<Rightarrow> t'" and
        "isFault t \<longrightarrow> isFault t'" and
        "t' = Fault f \<longrightarrow> t'=t" and
        "isFault t' \<longrightarrow> isFault t" and
        "\<not> isFault t' \<longrightarrow> t'=t"
        by blast
      with Normal True
      show ?thesis
        by (blast intro: execn.intros)
    qed
  qed
next
  case Throw thus ?case by auto
next
  case (Catch c1 c2 s n t)
  have exec_mark: "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards f (Catch c1 c2),s\<rangle> =n\<Rightarrow> t" by fact
  show ?case
  proof (cases "s")
    case (Fault f)
    with exec_mark have "t=Fault f"
      by (auto dest: execn_Fault_end)
    with Fault show ?thesis
      by auto
  next
    case Stuck
    with exec_mark have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with Stuck show ?thesis
      by auto
  next
    case (Abrupt s')
    with exec_mark have "t=Abrupt s'"
      by (auto dest: execn_Abrupt_end)
    with Abrupt show ?thesis
      by auto
  next
    case (Normal s') note s=this
    with exec_mark have 
      "\<Gamma>\<turnstile>\<^sub>p\<langle>Catch (mark_guards f c1) (mark_guards f c2),Normal s'\<rangle> =n\<Rightarrow> t" by simp
    thus ?thesis
    proof (cases)
      fix w
      assume exec_mark_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards f c1,Normal s'\<rangle> =n\<Rightarrow> Abrupt w"
      assume exec_mark_c2: "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards f c2,Normal w\<rangle> =n\<Rightarrow> t"
      from exec_mark_c1 Catch.hyps 
      obtain w' where 
        exec_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s'\<rangle> =n\<Rightarrow> w'" and
        w'_Fault_f: "w' = Fault f \<longrightarrow> w'=Abrupt w" and
        w'_Fault: "isFault w' \<longrightarrow> isFault (Abrupt w)" and
        w'_noFault: "\<not> isFault w' \<longrightarrow> w'=Abrupt w"
        by fastforce
      show ?thesis
      proof (cases "w'")
        case (Fault f')
        with Normal exec_c1 have "\<Gamma>\<turnstile>\<^sub>p\<langle>Catch c1 c2,s\<rangle> =n\<Rightarrow> Fault f'"
          by (auto intro: execn.intros)
        with w'_Fault Fault show ?thesis
          by auto
      next
        case Stuck
        with w'_noFault have False
          by simp
        thus ?thesis ..
      next
        case (Normal w'')
        with w'_noFault have False by simp thus ?thesis ..
      next
        case (Abrupt w'')
        with w'_noFault have w'': "w''=w" by simp
        from  exec_mark_c2 Catch.hyps 
        obtain t' where 
          "\<Gamma>\<turnstile>\<^sub>p\<langle>c2,Normal w\<rangle> =n\<Rightarrow> t'"
          "isFault t \<longrightarrow> isFault t'"
          "t' = Fault f \<longrightarrow> t'=t"
          "isFault t' \<longrightarrow> isFault t"
          "\<not> isFault t' \<longrightarrow> t'=t"
          by blast
        with w'' Abrupt s exec_c1
        show ?thesis
          by (blast intro: execn.intros)
      qed
    next
      assume t: "\<not> isAbr t"
      assume "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards f c1,Normal s'\<rangle> =n\<Rightarrow> t"
      with Catch.hyps 
      obtain t' where 
        exec_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s'\<rangle> =n\<Rightarrow> t'"  and
        t_Fault: "isFault t \<longrightarrow> isFault t'" and
        t'_Fault_f: "t' = Fault f \<longrightarrow> t'=t" and
        t'_Fault: "isFault t' \<longrightarrow> isFault t" and
        t'_noFault: "\<not> isFault t' \<longrightarrow> t'=t"
        by blast
      show ?thesis
      proof (cases "isFault t'")
        case True
        then obtain f' where t': "t'=Fault f'"..
        with exec_c1 have "\<Gamma>\<turnstile>\<^sub>p\<langle>Catch c1 c2,Normal s'\<rangle> =n\<Rightarrow> Fault f'" 
          by (auto intro: execn.intros)
        with t'_Fault_f t'_Fault t' s show ?thesis
          by auto
      next
        case False
        with t'_noFault have "t'=t" by simp
        with t exec_c1 s show ?thesis
          by (blast intro: execn.intros)
      qed
    qed
  qed
next
  case (Await b c e s n t)
  have exec_mark: " \<Gamma>\<turnstile>\<^sub>p \<langle>mark_guards f (Await b c e),s\<rangle> =n\<Rightarrow> t " by fact
  thus ?case 
  proof (cases s)
    case (Fault f)   
      with exec_mark have "t=s"
      by (auto dest: execn_Fault_end)
      thus ?thesis using Fault by auto
  next
    case Stuck  
      have "t = Stuck"
      using exec_mark Stuck execn_Stuck_end by blast
      thus ?thesis using Stuck by auto
  next
    case (Abrupt s')
    with exec_mark have "t=Abrupt s'"
      by (auto dest: execn_Abrupt_end)
    with Abrupt show ?thesis
      by auto
  next
   case (Normal s') note s=this   
    {
      fix c' r w
      assume exec_c': "\<Gamma>\<turnstile>\<^sub>p\<langle>c',r\<rangle> =n\<Rightarrow> w"
      assume c': "c'=Await b (Language.mark_guards f c) e"
      have "\<exists>w'. \<Gamma>\<turnstile>\<^sub>p\<langle>Await b c e,r\<rangle> =n\<Rightarrow> w' \<and> (isFault w \<longrightarrow> isFault w') \<and>
                   (w' = Fault f \<longrightarrow> w'=w) \<and> (isFault w' \<longrightarrow> isFault w) \<and>
                   (\<not> isFault w' \<longrightarrow> w'=w)"
        using exec_c' c'  
      proof (induct)
        case (AwaitTrue r b' \<Gamma>1 c'' n u) 
        then have eqs: "Await b' c'' e= Await b (Language.mark_guards f c) e" by auto
        from AwaitTrue.hyps eqs
        have r_in_b: "r\<in>b" by simp
        from AwaitTrue.hyps eqs
        have exec_mark_c: "\<Gamma>1\<turnstile>\<langle>Language.mark_guards f c,Normal r\<rangle> =n\<Rightarrow> u" by simp
        from AwaitTrue.hyps eqs
        have exec_mark_w: "\<Gamma>\<turnstile>\<^sub>p\<langle>Await b (Language.mark_guards f c) e,Normal r\<rangle> =n\<Rightarrow> u"         
        proof -
            have "\<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>c'',Normal r\<rangle> =n\<Rightarrow> u" using AwaitTrue.hyps(2) AwaitTrue.hyps(3) by presburger
            then have "\<Gamma>\<turnstile>\<^sub>p \<langle>Await b' c'' e,Normal r\<rangle> =n\<Rightarrow> u"
            by (fastforce intro: AwaitTrue.hyps(1) AwaitTrue.hyps(2) execn.AwaitTrue)
           thus ?thesis
           using eqs by auto
         qed        
        show ?case
        proof -
          from AwaitTrue.hyps eqs have "\<Gamma>1\<turnstile>\<langle>Language.mark_guards f c,Normal r\<rangle> =n\<Rightarrow> u"
            by simp
          
          obtain u' where 
            exec_c: "\<Gamma>1\<turnstile>\<langle>c,Normal r\<rangle> =n\<Rightarrow> u'" and
            u_Fault: "isFault u \<longrightarrow> isFault u'" and
            u'_Fault_f: "u' = Fault f \<longrightarrow> u'=u" and
            u'_Fault: "isFault u' \<longrightarrow> isFault u" and
            u'_noFault: "\<not> isFault u' \<longrightarrow> u'=u"
            by (metis Semantic.isFaultE SemanticCon.isFault_simps(3) exec_mark_c execn_mark_guards_to_execn)           
          show ?thesis
          proof (cases "isFault u'")
            case False
            with u'_noFault have u': "u'=u" by simp
            from AwaitTrue.hyps eqs obtain w' where
              "\<Gamma>\<turnstile>\<^sub>p\<langle>Await b c e,Normal r\<rangle> =n\<Rightarrow> w'"
              "isFault u  \<longrightarrow> isFault w'"
              "w' = Fault f \<longrightarrow> w'=u" 
              "isFault w' \<longrightarrow> isFault u" 
              "\<not> isFault w' \<longrightarrow> w' = u"
              proof -
                 assume a1: "\<And>w'. \<lbrakk>\<Gamma>\<turnstile>\<^sub>p \<langle>Await b c e,Normal r\<rangle> =n\<Rightarrow> w'; 
                                   isFault u \<longrightarrow> isFault w'; 
                                   w' = Fault f \<longrightarrow> w' = u; isFault w' \<longrightarrow> isFault u; 
                                   \<not> isFault w' \<longrightarrow> w' = u\<rbrakk> \<Longrightarrow> thesis"
                 have "\<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>c,Normal r\<rangle> =n\<Rightarrow> u'" using AwaitTrue.hyps(2) exec_c by blast
                 then have "\<Gamma>\<turnstile>\<^sub>p \<langle>Await b c e,Normal r\<rangle> =n\<Rightarrow> u'"
                 by (fastforce intro: exec_c execn.AwaitTrue r_in_b)
                 thus ?thesis
                 using a1 u' by blast
              qed
            with u' exec_c r_in_b 
            show ?thesis
              by (blast intro: execn.AwaitTrue)
          next
            case True
            then obtain f' where u': "u'=Fault f'"..
            with exec_c r_in_b 
            have exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>Await b c e,Normal r\<rangle> =n\<Rightarrow> Fault f'"
              by (simp add: AwaitTrue.hyps(2) execn.AwaitTrue)              
            from True u'_Fault have "isFault u"
              by simp
            then obtain f where u: "u=Fault f"..
            with exec_mark_w have "u=Fault f"
              by (auto)
            with exec u' u u'_Fault_f
            show ?thesis
              by auto
          qed
        qed
      next
        case (AwaitFalse s b) thus ?case using execn.AwaitFalse by fastforce
      qed auto  
    } note hyp_await = this 
    show ?thesis using exec_mark hyp_await by auto
  qed
qed

lemma exec_to_exec_mark_guards:
 assumes exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t" 
 assumes t_not_Fault: "\<not> isFault t"
 shows "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards f c,s\<rangle> \<Rightarrow> t "
proof -
  from exec_to_execn [OF exec_c] obtain n where
    "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" ..
  from execn_to_execn_mark_guards [OF this t_not_Fault]
  show ?thesis
    by (blast intro: execn_to_exec)
qed

lemma exec_to_exec_mark_guards_Fault:
 assumes exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> Fault f"
 shows "\<exists>f'. \<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards x c,s\<rangle> \<Rightarrow> Fault f'"
proof -
  from exec_to_execn [OF exec_c] obtain n where
    "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> Fault f" ..
  from execn_to_execn_mark_guards_Fault [OF this]
  show ?thesis
    by (blast intro: execn_to_exec)
qed


lemma exec_mark_guards_to_exec:
  assumes exec_mark: "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards f c,s\<rangle> \<Rightarrow> t"
  shows "\<exists>t'. \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t' \<and> 
            (isFault t \<longrightarrow> isFault t') \<and> 
            (t' = Fault f \<longrightarrow> t'=t) \<and>
            (isFault t' \<longrightarrow> isFault t) \<and>
            (\<not> isFault t' \<longrightarrow> t'=t)"
proof -
  from exec_to_execn [OF exec_mark] obtain n where
    "\<Gamma>\<turnstile>\<^sub>p\<langle>mark_guards f c,s\<rangle> =n\<Rightarrow> t" ..
  from execn_mark_guards_to_execn [OF this]
  show ?thesis
    by (blast intro: execn_to_exec)
qed

(* ************************************************************************* *)
subsection {* Lemmas about @{const "strip_guards"} *}
(* ************************************************************************* *)

lemma execn_to_execn_strip_guards:
 assumes exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" 
 assumes t_not_Fault: "\<not> isFault t"
 shows "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,s\<rangle> =n\<Rightarrow> t "
using exec_c t_not_Fault [simplified not_isFault_iff]
proof induct
 case (AwaitTrue s b \<Gamma>1 c n t)
 then have "\<Gamma>1\<turnstile> \<langle>Language.strip_guards F c,Normal s\<rangle> =n\<Rightarrow> t"
      by (meson Semantic.isFaultE execn_to_execn_strip_guards)
 thus ?case by (auto intro:AwaitTrue.hyps(1) AwaitTrue.hyps(2) execn.AwaitTrue)
qed (auto intro: execn.intros dest: noFaultn_startD')


lemma execn_to_execn_strip_guards_Fault:
 assumes exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"
 shows "\<And>f. \<lbrakk>t=Fault f; f \<notin> F\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,s\<rangle> =n\<Rightarrow> Fault f"
using exec_c 
proof (induct)
  case Skip thus ?case by auto
next
  case Guard thus ?case by (fastforce intro: execn.intros)
next
  case GuardFault thus ?case by (fastforce intro: execn.intros)
next
  case FaultProp thus ?case by auto
next
 case Basic thus ?case by auto
next
 case Spec thus ?case by auto
next
 case SpecStuck thus ?case by auto
next
  case (Seq c1 s n w c2 t)
  have exec_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> =n\<Rightarrow> w" by fact
  have exec_c2: "\<Gamma>\<turnstile>\<^sub>p\<langle>c2,w\<rangle> =n\<Rightarrow> t" by fact
  have t: "t=Fault f" by fact
  have notinF: "f \<notin> F" by fact
  show ?case
  proof (cases w)
    case (Fault f')
    with exec_c2 t have "f'=f"
      by (auto dest: execn_Fault_end)
    with Fault notinF Seq.hyps 
    have "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c1,Normal s\<rangle> =n\<Rightarrow> Fault f"
      by auto
    moreover have "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c2,Fault f\<rangle> =n\<Rightarrow> Fault f"
      by auto
    ultimately show ?thesis
      by (auto intro: execn.intros)
  next
    case (Normal s')
    with execn_to_execn_strip_guards [OF exec_c1] 
    have exec_strip_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c1,Normal s\<rangle> =n\<Rightarrow> w"
      by simp
    with Seq.hyps t notinF 
    have "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c2,w\<rangle> =n\<Rightarrow> Fault f" 
      by blast
    with exec_strip_c1 show ?thesis
      by (auto intro: execn.intros)
  next
    case (Abrupt s')
    with execn_to_execn_strip_guards [OF exec_c1] 
    have exec_strip_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c1,Normal s\<rangle> =n\<Rightarrow> w"
      by simp
    with Seq.hyps t notinF 
    have "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c2,w\<rangle> =n\<Rightarrow> Fault f" 
      by (auto intro: execn.intros)
    with exec_strip_c1 show ?thesis
      by (auto intro: execn.intros)
  next
    case Stuck
    with exec_c2 have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with t show ?thesis by simp
  qed
next
  case CondTrue thus ?case by (fastforce intro: execn.intros)
next
  case CondFalse thus ?case by (fastforce intro: execn.intros)
next
  case (WhileTrue s b c n w t) 
  have exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> w" by fact
  have exec_w: "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,w\<rangle> =n\<Rightarrow> t" by fact
  have t: "t = Fault f" by fact
  have notinF: "f \<notin> F" by fact
  have s_in_b: "s \<in> b" by fact
  show ?case
  proof (cases w)
    case (Fault f')
    with exec_w t have "f'=f"
      by (auto dest: execn_Fault_end)
    with Fault notinF WhileTrue.hyps 
    have "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,Normal s\<rangle> =n\<Rightarrow> Fault f"
      by auto
    moreover have "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F (While b c),Fault f\<rangle> =n\<Rightarrow> Fault f"
      by auto
    ultimately show ?thesis
      using s_in_b by (auto intro: execn.intros)
  next
    case (Normal s')
    with execn_to_execn_strip_guards [OF exec_c] 
    have exec_strip_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,Normal s\<rangle> =n\<Rightarrow> w"
      by simp
    with WhileTrue.hyps t notinF 
    have "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F (While b c),w\<rangle> =n\<Rightarrow> Fault f" 
      by blast
    with exec_strip_c s_in_b show ?thesis
      by (auto intro: execn.intros)
  next
    case (Abrupt s')
    with execn_to_execn_strip_guards [OF exec_c] 
    have exec_strip_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,Normal s\<rangle> =n\<Rightarrow> w"
      by simp
    with WhileTrue.hyps t notinF 
    have "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F (While b c),w\<rangle> =n\<Rightarrow> Fault f" 
      by (auto intro: execn.intros)
    with exec_strip_c s_in_b show ?thesis
      by (auto intro: execn.intros)
  next
    case Stuck
    with exec_w have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with t show ?thesis by simp
  qed
next
  case WhileFalse thus ?case by (fastforce intro: execn.intros)
next
  case Call thus ?case by (fastforce intro: execn.intros)
next
  case CallUndefined thus ?case by simp
next
  case StuckProp thus ?case by simp
next
  case DynCom thus ?case by (fastforce intro: execn.intros)
next
  case Throw thus ?case by simp
next
  case AbruptProp thus ?case by simp
next
  case (CatchMatch c1 s n w c2 t) 
  have exec_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> =n\<Rightarrow> Abrupt w" by fact
  have exec_c2: "\<Gamma>\<turnstile>\<^sub>p\<langle>c2,Normal w\<rangle> =n\<Rightarrow> t" by fact
  have t: "t = Fault f" by fact
  have notinF: "f \<notin> F" by fact
  from execn_to_execn_strip_guards [OF exec_c1]
  have exec_strip_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c1,Normal s\<rangle> =n\<Rightarrow> Abrupt w"
    by simp
  with CatchMatch.hyps t notinF 
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c2,Normal w\<rangle> =n\<Rightarrow> Fault f" 
    by blast
  with exec_strip_c1 show ?case
    by (auto intro: execn.intros)
next
  case CatchMiss thus ?case by (fastforce intro: execn.intros)
next
  case (AwaitTrue s b \<Gamma>1 c n t)
  then have "\<Gamma>1\<turnstile>\<langle>Language.strip_guards F c,Normal s\<rangle> =n\<Rightarrow> Fault f"
       by (simp add: execn_to_execn_strip_guards_Fault) 
  then  have "\<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Language.strip_guards F c,Normal s\<rangle> =n\<Rightarrow> Fault f" using AwaitTrue.hyps(2) AwaitTrue.hyps(3) using AwaitTrue.prems(1) by blast 
  thus ?case by(simp add: AwaitTrue.hyps(1) execn.AwaitTrue)
next
  case (AwaitFalse s b) thus ?case by (auto simp add:execn.AwaitFalse)
qed

lemma execn_to_execn_strip_guards':
 assumes exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" 
 assumes t_not_Fault: "t \<notin> Fault ` F"
 shows "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,s\<rangle> =n\<Rightarrow> t"
proof (cases t)
  case (Fault f)
  with t_not_Fault exec_c show ?thesis 
    by (auto intro: execn_to_execn_strip_guards_Fault)
qed (insert exec_c, auto intro: execn_to_execn_strip_guards)
  
lemma execn_strip_guards_to_execn:
  "\<And>s n t. \<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,s\<rangle> =n\<Rightarrow> t
  \<Longrightarrow> \<exists>t'. \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t' \<and> 
            (isFault t \<longrightarrow> isFault t') \<and> 
            (t' \<in> Fault ` (- F) \<longrightarrow> t'=t) \<and>
            (\<not> isFault t' \<longrightarrow> t'=t)"
proof (induct c)
  case Skip thus ?case by auto
next
  case Basic thus ?case by auto
next
  case Spec thus ?case by auto
next
  case (Seq c1 c2 s n t)
  have exec_strip: "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F (Seq c1 c2),s\<rangle> =n\<Rightarrow> t" by fact
  then obtain w where 
    exec_strip_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c1,s\<rangle> =n\<Rightarrow> w" and
    exec_strip_c2: "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c2,w\<rangle> =n\<Rightarrow> t"
    by (auto elim: execn_elim_cases)
  from Seq.hyps exec_strip_c1
  obtain w' where 
    exec_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,s\<rangle> =n\<Rightarrow> w'" and
    w_Fault: "isFault w \<longrightarrow> isFault w'" and
    w'_Fault: "w' \<in> Fault ` (- F) \<longrightarrow> w'=w" and
    w'_noFault: "\<not> isFault w' \<longrightarrow> w'=w"
    by blast
  show ?case
  proof (cases "s")
    case (Fault f)
    with exec_strip have "t=Fault f"
      by (auto dest: execn_Fault_end)
    with Fault show ?thesis
      by auto
  next
    case Stuck
    with exec_strip have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with Stuck show ?thesis
      by auto
  next
    case (Abrupt s')
    with exec_strip have "t=Abrupt s'"
      by (auto dest: execn_Abrupt_end)
    with Abrupt show ?thesis
      by auto
  next
    case (Normal s')
    show ?thesis
    proof (cases "isFault w")
      case True
      then obtain f where w': "w=Fault f"..
      moreover with exec_strip_c2 
      have t: "t=Fault f"
        by (auto dest: execn_Fault_end)
      ultimately show ?thesis
        using Normal w_Fault w'_Fault exec_c1
        by (fastforce intro: execn.intros elim: isFaultE)      
    next
      case False
      note noFault_w = this
      show ?thesis
      proof (cases "isFault w'")
        case True
        then obtain f' where w': "w'=Fault f'"..
        with Normal exec_c1 
        have exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>Seq c1 c2,s\<rangle> =n\<Rightarrow> Fault f'"
          by (auto intro: execn.intros)
        from w'_Fault w' noFault_w
        have "f' \<in> F"
          by (cases w) auto
        with exec 
        show ?thesis
          by auto
      next
        case False
        with w'_noFault have w': "w'=w" by simp
        from Seq.hyps exec_strip_c2
        obtain t' where
          "\<Gamma>\<turnstile>\<^sub>p\<langle>c2,w\<rangle> =n\<Rightarrow> t'" and
          "isFault t \<longrightarrow> isFault t'" and
          "t' \<in> Fault ` (-F) \<longrightarrow> t'=t" and
          "\<not> isFault t' \<longrightarrow> t'=t"
          by blast
        with Normal exec_c1 w'
        show ?thesis
          by (fastforce intro: execn.intros)
      qed
    qed
  qed
next
next
  case (Cond b c1 c2 s n t)
  have exec_strip: "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F (Cond b c1 c2),s\<rangle> =n\<Rightarrow> t" by fact
  show ?case
  proof (cases s)
    case (Fault f)
    with exec_strip have "t=Fault f"
      by (auto dest: execn_Fault_end)
    with Fault show ?thesis
      by auto
  next
    case Stuck
    with exec_strip have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with Stuck show ?thesis
      by auto
  next
    case (Abrupt s')
    with exec_strip have "t=Abrupt s'"
      by (auto dest: execn_Abrupt_end)
    with Abrupt show ?thesis
      by auto
  next
    case (Normal s')
    show ?thesis
    proof (cases "s'\<in> b")
      case True
      with Normal exec_strip
      have "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c1 ,Normal s'\<rangle> =n\<Rightarrow> t"
        by (auto elim: execn_Normal_elim_cases)
      with Normal True Cond.hyps obtain t'
        where "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s'\<rangle> =n\<Rightarrow> t'" 
            "isFault t \<longrightarrow> isFault t'" 
            "t' \<in> Fault ` (-F) \<longrightarrow> t'=t"
            "\<not> isFault t' \<longrightarrow> t' = t"
        by blast
      with Normal True
      show ?thesis
        by (blast intro: execn.intros)
    next
      case False
      with Normal exec_strip
      have "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c2 ,Normal s'\<rangle> =n\<Rightarrow> t"
        by (auto elim: execn_Normal_elim_cases)
      with Normal False Cond.hyps obtain t'
        where "\<Gamma>\<turnstile>\<^sub>p\<langle>c2,Normal s'\<rangle> =n\<Rightarrow> t'" 
            "isFault t  \<longrightarrow> isFault t'" 
            "t' \<in> Fault ` (-F) \<longrightarrow> t'=t"
            "\<not> isFault t' \<longrightarrow> t' = t"
        by blast
      with Normal False
      show ?thesis
        by (blast intro: execn.intros)
    qed
  qed
next
  case (While b c s n t)
  have exec_strip: "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F (While b c),s\<rangle> =n\<Rightarrow> t" by fact
  show ?case
  proof (cases s)
    case (Fault f)
    with exec_strip have "t=Fault f"
      by (auto dest: execn_Fault_end)
    with Fault show ?thesis
      by auto
  next
    case Stuck
    with exec_strip have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with Stuck show ?thesis
      by auto
  next
    case (Abrupt s')
    with exec_strip have "t=Abrupt s'"
      by (auto dest: execn_Abrupt_end)
    with Abrupt show ?thesis
      by auto
  next
    case (Normal s')
    {
      fix c' r w
      assume exec_c': "\<Gamma>\<turnstile>\<^sub>p\<langle>c',r\<rangle> =n\<Rightarrow> w"
      assume c': "c'=While b (strip_guards F c)"
      have "\<exists>w'. \<Gamma>\<turnstile>\<^sub>p\<langle>While b c,r\<rangle> =n\<Rightarrow> w' \<and> (isFault w \<longrightarrow> isFault w') \<and>
                   (w' \<in> Fault ` (-F) \<longrightarrow> w'=w) \<and>
                   (\<not> isFault w' \<longrightarrow> w'=w)"
        using exec_c' c' 
      proof (induct)
        case (WhileTrue r b' c'' n u w)
        have eqs: "While b' c'' = While b (strip_guards F c)" by fact
        from WhileTrue.hyps eqs
        have r_in_b: "r\<in>b" by simp
        from WhileTrue.hyps eqs
        have exec_strip_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,Normal r\<rangle> =n\<Rightarrow> u" by simp
        from WhileTrue.hyps eqs
        have exec_strip_w: "\<Gamma>\<turnstile>\<^sub>p\<langle>While b (strip_guards F c),u\<rangle> =n\<Rightarrow> w"
          by simp
        show ?case
        proof -
          from WhileTrue.hyps eqs have "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,Normal r\<rangle> =n\<Rightarrow> u"
            by simp
          with While.hyps
          obtain u' where 
            exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal r\<rangle> =n\<Rightarrow> u'" and
            u_Fault: "isFault u \<longrightarrow> isFault u'" and
            u'_Fault: "u' \<in> Fault ` (-F) \<longrightarrow> u'=u" and
            u'_noFault: "\<not> isFault u' \<longrightarrow> u'=u"
            by blast
          show ?thesis
          proof (cases "isFault u'")
            case False
            with u'_noFault have u': "u'=u" by simp
            from WhileTrue.hyps eqs obtain w' where
              "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,u\<rangle> =n\<Rightarrow> w'"
              "isFault w  \<longrightarrow> isFault w'"
              "w' \<in> Fault ` (-F) \<longrightarrow> w'=w" 
              "\<not> isFault w' \<longrightarrow> w' = w"
              by auto
            with u' exec_c r_in_b 
            show ?thesis
              by (blast intro: execn.WhileTrue)
          next
            case True
            then obtain f' where u': "u'=Fault f'"..
            with exec_c r_in_b 
            have exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,Normal r\<rangle> =n\<Rightarrow> Fault f'"
              by (blast intro: execn.intros)
            show ?thesis
            proof (cases "isFault u")
              case True
              then obtain f where u: "u=Fault f"..
              with exec_strip_w have "w=Fault f"
                by (auto dest: execn_Fault_end)
              with exec u' u u'_Fault
              show ?thesis
                by auto
            next
              case False
              with u'_Fault u' have "f' \<in> F"
                by (cases u) auto
              with exec show ?thesis
                by auto
            qed
          qed
        qed
      next
        case (WhileFalse r b' c'' n)
        have eqs: "While b'  c'' = While b (strip_guards F c)" by fact
        from WhileFalse.hyps eqs
        have r_not_in_b: "r\<notin>b" by simp
        show ?case
        proof -
          from r_not_in_b 
          have "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,Normal r\<rangle> =n\<Rightarrow> Normal r"
            by (rule execn.WhileFalse)
          thus ?thesis
            by blast
        qed
      qed auto
    } note hyp_while = this
    show ?thesis
    proof (cases "s'\<in>b") 
      case False
      with Normal exec_strip
      have "t=s"
        by (auto elim: execn_Normal_elim_cases)
      with Normal False show ?thesis
        by (auto intro: execn.intros)
    next
      case True note s'_in_b = this
      with Normal exec_strip obtain r where
        exec_strip_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,Normal s'\<rangle> =n\<Rightarrow> r" and
        exec_strip_w: "\<Gamma>\<turnstile>\<^sub>p\<langle>While b (strip_guards F c),r\<rangle> =n\<Rightarrow> t"
        by (auto elim: execn_Normal_elim_cases)
      from While.hyps exec_strip_c obtain r' where 
        exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s'\<rangle> =n\<Rightarrow> r'" and
        r_Fault: "isFault r \<longrightarrow> isFault r'" and
        r'_Fault: "r' \<in> Fault ` (-F) \<longrightarrow> r'=r" and
        r'_noFault: "\<not> isFault r' \<longrightarrow> r'=r"
        by blast
      show ?thesis
      proof (cases "isFault r'")
        case False
        with r'_noFault have r': "r'=r" by simp
        from hyp_while exec_strip_w 
        obtain t' where
          "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,r\<rangle> =n\<Rightarrow> t'"
          "isFault t \<longrightarrow> isFault t'"
          "t' \<in> Fault ` (-F) \<longrightarrow> t'=t"
          "\<not> isFault t' \<longrightarrow> t'=t"
          by blast
        with r' exec_c Normal s'_in_b
        show ?thesis
          by (blast intro: execn.intros)
      next
        case True
        then obtain f' where r': "r'=Fault f'"..
        hence "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,r'\<rangle> =n\<Rightarrow> Fault f'"
          by auto 
        with Normal s'_in_b exec_c
        have exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,Normal s'\<rangle> =n\<Rightarrow> Fault f'"
          by (auto intro: execn.intros)
        show ?thesis
        proof (cases "isFault r")
          case True
          then obtain f where r: "r=Fault f"..
          with exec_strip_w have "t=Fault f"
            by (auto dest: execn_Fault_end)
          with Normal exec r' r r'_Fault
          show ?thesis
            by auto
        next
          case False
          with r'_Fault r' have "f' \<in> F"
            by (cases r) auto
          with Normal exec show ?thesis
            by auto
        qed
      qed
    qed
  qed
next
  case Call thus ?case by auto
next
  case DynCom thus ?case 
    by (fastforce elim!: execn_elim_cases intro: execn.intros)
next
  case (Guard f g c s n t)
  have exec_strip: "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F (Guard f g c),s\<rangle> =n\<Rightarrow> t" by fact
  show ?case
  proof (cases s)
    case (Fault f)
    with exec_strip have "t=Fault f"
      by (auto dest: execn_Fault_end)
    with Fault show ?thesis
      by auto
  next
    case Stuck
    with exec_strip have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with Stuck show ?thesis
      by auto
  next
    case (Abrupt s')
    with exec_strip have "t=Abrupt s'"
      by (auto dest: execn_Abrupt_end)
    with Abrupt show ?thesis
      by auto
  next
    case (Normal s')
    show ?thesis
    proof (cases "f\<in>F")
      case True
      with exec_strip Normal 
      have exec_strip_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,Normal s'\<rangle> =n\<Rightarrow> t"
        by simp
      with Guard.hyps obtain t' where
        "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s'\<rangle> =n\<Rightarrow> t'" and
        "isFault t \<longrightarrow> isFault t'" and
        "t' \<in> Fault ` (-F) \<longrightarrow> t'=t" and
        "\<not> isFault t' \<longrightarrow> t'=t"
        by blast
      with Normal True 
      show ?thesis
        by (cases "s'\<in> g") (fastforce intro: execn.intros)+
    next
      case False
      note f_notin_F = this
      show ?thesis
      proof (cases "s'\<in>g")
        case False
        with Normal exec_strip f_notin_F have t: "t=Fault f"
          by (auto elim: execn_Normal_elim_cases)
        from False
        have "\<Gamma>\<turnstile>\<^sub>p\<langle>Guard f g c,Normal s'\<rangle> =n\<Rightarrow> Fault f"
          by (blast intro: execn.intros)
        with False Normal t show ?thesis
          by auto
      next
        case True
        with exec_strip Normal f_notin_F
        have "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,Normal s'\<rangle> =n\<Rightarrow> t"
          by (auto elim: execn_Normal_elim_cases)
        with Guard.hyps obtain t' where
          "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s'\<rangle> =n\<Rightarrow> t'" and
          "isFault t \<longrightarrow> isFault t'" and
          "t' \<in> Fault ` (-F) \<longrightarrow> t'=t" and
          "\<not> isFault t' \<longrightarrow> t'=t"
          by blast
        with Normal True
        show ?thesis
          by (blast intro: execn.intros)
      qed
    qed
  qed
next
  case Throw thus ?case by auto
next
  case (Catch c1 c2 s n t)
  have exec_strip: "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F (Catch c1 c2),s\<rangle> =n\<Rightarrow> t" by fact
  show ?case
  proof (cases "s")
    case (Fault f)
    with exec_strip have "t=Fault f"
      by (auto dest: execn_Fault_end)
    with Fault show ?thesis
      by auto
  next
    case Stuck
    with exec_strip have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with Stuck show ?thesis
      by auto
  next
    case (Abrupt s')
    with exec_strip have "t=Abrupt s'"
      by (auto dest: execn_Abrupt_end)
    with Abrupt show ?thesis
      by auto
  next
    case (Normal s') note s=this
    with exec_strip have 
      "\<Gamma>\<turnstile>\<^sub>p\<langle>Catch (strip_guards F c1) (strip_guards F c2),Normal s'\<rangle> =n\<Rightarrow> t" by simp
    thus ?thesis
    proof (cases)
      fix w
      assume exec_strip_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c1,Normal s'\<rangle> =n\<Rightarrow> Abrupt w"
      assume exec_strip_c2: "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c2,Normal w\<rangle> =n\<Rightarrow> t"
      from exec_strip_c1 Catch.hyps 
      obtain w' where 
        exec_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s'\<rangle> =n\<Rightarrow> w'" and
        w'_Fault: "w' \<in> Fault ` (-F) \<longrightarrow> w'=Abrupt w" and
        w'_noFault: "\<not> isFault w' \<longrightarrow> w'=Abrupt w"
        by blast
      show ?thesis
      proof (cases "w'")
        case (Fault f')
        with Normal exec_c1 have "\<Gamma>\<turnstile>\<^sub>p\<langle>Catch c1 c2,s\<rangle> =n\<Rightarrow> Fault f'"
          by (auto intro: execn.intros)
        with w'_Fault Fault show ?thesis
          by auto
      next
        case Stuck
        with w'_noFault have False
          by simp
        thus ?thesis ..
      next
        case (Normal w'')
        with w'_noFault have False by simp thus ?thesis ..
      next
        case (Abrupt w'')
        with w'_noFault have w'': "w''=w" by simp
        from  exec_strip_c2 Catch.hyps 
        obtain t' where 
          "\<Gamma>\<turnstile>\<^sub>p\<langle>c2,Normal w\<rangle> =n\<Rightarrow> t'"
          "isFault t \<longrightarrow> isFault t'"
          "t' \<in> Fault ` (-F) \<longrightarrow> t'=t"
          "\<not> isFault t' \<longrightarrow> t'=t"
          by blast
        with w'' Abrupt s exec_c1
        show ?thesis
          by (blast intro: execn.intros)
      qed
    next
      assume t: "\<not> isAbr t"
      assume "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c1,Normal s'\<rangle> =n\<Rightarrow> t"
      with Catch.hyps 
      obtain t' where 
        exec_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s'\<rangle> =n\<Rightarrow> t'"  and
        t_Fault: "isFault t \<longrightarrow> isFault t'" and
        t'_Fault: "t' \<in> Fault ` (-F) \<longrightarrow> t'=t" and
        t'_noFault: "\<not> isFault t' \<longrightarrow> t'=t"
        by blast
      show ?thesis
      proof (cases "isFault t'")
        case True
        then obtain f' where t': "t'=Fault f'"..
        with exec_c1 have "\<Gamma>\<turnstile>\<^sub>p\<langle>Catch c1 c2,Normal s'\<rangle> =n\<Rightarrow> Fault f'" 
          by (auto intro: execn.intros)
        with t'_Fault t' s show ?thesis
          by auto
      next
        case False
        with t'_noFault have "t'=t" by simp
        with t exec_c1 s show ?thesis
          by (blast intro: execn.intros)
      qed
    qed
  qed
next
  case (Await b c e s n t) 
  have exec_strip: "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F (Await b c e),s\<rangle> =n\<Rightarrow> t" by fact
  thus ?case
  proof (cases s)
  case (Fault f) 
    with exec_strip have "t=Fault f"
      by (auto dest: execn_Fault_end)
    with Fault show ?thesis
      by auto
  next
    case Stuck
    with exec_strip have "t=Stuck"
      by (auto dest: execn_Stuck_end)
    with Stuck show ?thesis
      by auto
  next
    case (Abrupt s')
    with exec_strip have "t=Abrupt s'"
      by (auto dest: execn_Abrupt_end)
    with Abrupt show ?thesis
      by auto
  next
    case (Normal s')
     with exec_strip have 
      "\<Gamma>\<turnstile>\<^sub>p\<langle>Await b (Language.strip_guards F c) e,Normal s'\<rangle> =n\<Rightarrow> t" by simp
      {
      fix c' r w
      assume exec_c': "\<Gamma>\<turnstile>\<^sub>p\<langle>c',r\<rangle> =n\<Rightarrow> w"
      assume c': "c'=Await b (Language.strip_guards F c) e"
      have "\<exists>w'. \<Gamma>\<turnstile>\<^sub>p\<langle>Await b c e,r\<rangle> =n\<Rightarrow> w' \<and> (isFault w \<longrightarrow> isFault w') \<and>
                   (w' \<in> Fault ` (-F) \<longrightarrow> w'=w) \<and>
                   (\<not> isFault w' \<longrightarrow> w'=w)"
        using exec_c' c' 
      proof (induct)
        case (AwaitTrue r b' \<Gamma>1 c'' n u e)
        then have eqs: "Await b' c'' e = Await b (Language.strip_guards F c) e" by auto
        from AwaitTrue.hyps eqs
        have r_in_b: "r\<in>b" by simp
        from AwaitTrue.hyps eqs
        have exec_strip_c: "\<Gamma>1\<turnstile>\<langle>Language.strip_guards F c,Normal r\<rangle> =n\<Rightarrow> u" by simp
        from AwaitTrue.hyps eqs
        have beq:"b=b'" by auto
        from AwaitTrue.hyps eqs beq
        have exec_c'': "\<Gamma>\<turnstile>\<^sub>p \<langle>Await b' c'' e,Normal r\<rangle> =n\<Rightarrow> u" by (simp add: execn.AwaitTrue)  
        from AwaitTrue.hyps eqs exec_c''
        have exec_strip_w: "\<Gamma>\<turnstile>\<^sub>p\<langle>Await b (Language.strip_guards F c) e,Normal r\<rangle> =n\<Rightarrow> u"
          by simp
        show ?case
        proof -
          from AwaitTrue.hyps eqs have "\<Gamma>1\<turnstile>\<langle>Language.strip_guards F c,Normal r\<rangle> =n\<Rightarrow> u"
            by simp          
          obtain u' where 
            exec_c: "\<Gamma>1\<turnstile>\<langle>c,Normal r\<rangle> =n\<Rightarrow> u'" and
            u_Fault: "isFault u \<longrightarrow> isFault u'" and
            u'_Fault: "u' \<in> Fault ` (-F) \<longrightarrow> u'=u" and
            u'_noFault: "\<not> isFault u' \<longrightarrow> u'=u"
            by (metis Semantic.isFaultE SemanticCon.isFault_simps(3) exec_strip_c execn_strip_guards_to_execn)                       
          show ?thesis by (metis (no_types) AwaitTrue.hyps(2) exec_c execn.AwaitTrue r_in_b u'_Fault u'_noFault) 
        qed
      next 
        case (AwaitFalse s b) thus ?case using execn.AwaitFalse by fastforce      
      qed auto
    } note hyp_while = this
    thus ?thesis using Await.prems by auto
  qed
qed

lemma  noaw_strip_noaw: 
       assumes noawait:"noawaits (LanguageCon.strip_guards F z)"
       shows "noawaits z"
using noawait
proof (induct z)
 case Skip then show ?case by fastforce
next
 case Basic then show ?case by fastforce
next
 case Spec then show ?case by fastforce
next
 case Seq then show ?case by fastforce
next
 case Cond then show ?case by simp
next
 case While then show ?case by simp
next
 case Call then show ?case by fastforce
next
 case DynCom then show ?case by fastforce
next
 case (Guard f g c)  
 have "noawaits (LanguageCon.strip_guards F c)" 
 proof (cases "f\<in>F")
   case True show ?thesis using Guard.prems True by force 
 next
   case False thus ?thesis 
   using strip_guards_simps(9) noawaits.simps(9) Guard.prems
   by fastforce  
 qed
 thus ?case
   by (simp add: Guard.hyps) 
next
  case (Throw) then show ?case by fastforce
next
  case (Catch) then show ?case by fastforce
qed fastforce

lemma await_strip_noaw_z_F:"\<not> noawaits (LanguageCon.strip_guards F z)
          \<Longrightarrow> noawaits z \<Longrightarrow> P"
proof (induct z)
 case Skip thus ?case by auto
next
 case Basic then show ?case by fastforce
next
 case Spec then show ?case by fastforce
next
 case Seq then show ?case by fastforce
next
 case Cond then show ?case by fastforce
next
 case While then show ?case by fastforce
next
 case Call then show ?case by fastforce
next
 case DynCom then show ?case by fastforce
next
 case (Guard f g c) 
 then have "noawaits c" using Guard.prems(2) by auto  
 have "\<not> noawaits (LanguageCon.strip_guards F c)"
 proof (cases "f\<in>F")
    case True thus ?thesis using Guard.prems by force
 next
   case False thus ?thesis 
   using strip_guards_simps(9) noawaits.simps(9) Guard.prems
   by fastforce
 qed
 thus ?thesis
    using Guard.hyps `noawaits c` by blast     
next
  case (Throw) then show ?case by fastforce
next
  case (Catch) then show ?case by fastforce
qed fastforce

lemma strip_eq: "(strip F \<Gamma>)\<^sub>\<not>\<^sub>a = Language.strip F (\<Gamma>\<^sub>\<not>\<^sub>a)"
unfolding Language.strip_def LanguageCon.strip_def no_await_body_def
apply rule
apply (split option.split)
apply auto
apply (simp add: no_await_strip_guards_eq) 
apply (rule  noaw_strip_noaw, assumption)
apply (rule await_strip_noaw_z_F)
by assumption

lemma execn_strip_to_execn:
  assumes exec_strip: "(strip F \<Gamma>)\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"
  shows "\<exists>t'. \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t' \<and> 
                 (isFault t \<longrightarrow> isFault t') \<and> 
                 (t' \<in> Fault ` (- F) \<longrightarrow> t'=t) \<and>
                 (\<not> isFault t' \<longrightarrow> t'=t)"
using exec_strip
proof (induct)
  case Skip thus ?case by (blast intro: execn.intros)
next
  case Guard thus ?case by (blast intro: execn.intros)
next
  case GuardFault thus ?case by (blast intro: execn.intros)
next
  case FaultProp thus ?case by (blast intro: execn.intros)
next
  case Basic thus ?case by (blast intro: execn.intros)
next
  case Spec thus ?case by (blast intro: execn.intros)
next
  case SpecStuck thus ?case by (blast intro: execn.intros)
next
  case Seq thus ?case by (blast intro: execn.intros elim: isFaultE)
next
  case CondTrue thus ?case by (blast intro: execn.intros)
next
  case CondFalse thus ?case by (blast intro: execn.intros)
next
  case WhileTrue thus ?case by (blast intro: execn.intros elim: isFaultE)
next
  case WhileFalse thus ?case by (blast intro: execn.intros)
next
  case Call thus ?case
    by simp (blast intro: execn.intros dest: execn_strip_guards_to_execn)
next
  case CallUndefined thus ?case
    by simp (blast intro: execn.intros)
next
  case StuckProp thus ?case
    by blast
next
  case DynCom thus ?case by (blast intro: execn.intros)
next
  case Throw thus ?case by (blast intro: execn.intros)
next
  case AbruptProp thus ?case by (blast intro: execn.intros)
next
  case (CatchMatch c1 s n r c2 t)
  then obtain r' t' where 
    exec_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> =n\<Rightarrow> r'"  and
    r'_Fault: "r' \<in> Fault ` (-F) \<longrightarrow> r' = Abrupt r" and
    r'_noFault: "\<not> isFault r' \<longrightarrow> r' = Abrupt r" and
    exec_c2: "\<Gamma>\<turnstile>\<^sub>p\<langle>c2,Normal r\<rangle> =n\<Rightarrow> t'" and
    t_Fault: "isFault t \<longrightarrow> isFault t'" and
    t'_Fault: "t' \<in> Fault ` (-F) \<longrightarrow> t' = t" and
    t'_noFault: "\<not> isFault t' \<longrightarrow> t' = t"
    by blast
  show ?case
  proof (cases "isFault r'")
    case True
    then obtain f' where r': "r'=Fault f'"..
    with exec_c1 have "\<Gamma>\<turnstile>\<^sub>p\<langle>Catch c1 c2,Normal s\<rangle> =n\<Rightarrow> Fault f'"
      by (auto intro: execn.intros)
    with r' r'_Fault show ?thesis
      by (auto intro: execn.intros)
  next
    case False
    with r'_noFault have "r'=Abrupt r" by simp
    with exec_c1 exec_c2 t_Fault t'_noFault t'_Fault
    show ?thesis 
      by (blast intro: execn.intros)
  qed
next  
  case CatchMiss thus ?case by (fastforce intro: execn.intros elim: isFaultE) 
next 
  case AwaitTrue thus ?case 
    by (metis Semantic.isFaultE SemanticCon.isFault_simps(3) execn.AwaitTrue execn_strip_to_execn strip_eq) 
next
  case AwaitFalse thus ?case by (fastforce intro: execn.intros(14))
qed 

lemma exec_strip_guards_to_exec: 
  assumes exec_strip: "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,s\<rangle> \<Rightarrow> t" 
  shows "\<exists>t'. \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t' \<and> 
              (isFault t \<longrightarrow> isFault t') \<and> 
              (t' \<in> Fault ` (-F) \<longrightarrow> t'=t) \<and>
              (\<not> isFault t' \<longrightarrow> t'=t)"
proof -
  from exec_strip obtain n where 
    execn_strip: "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,s\<rangle> =n\<Rightarrow> t"
    by (auto simp add: exec_iff_execn)
  then obtain t' where
    "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t'"  
    "isFault t \<longrightarrow> isFault t'" "t' \<in> Fault ` (-F) \<longrightarrow> t'=t" "\<not> isFault t' \<longrightarrow> t'=t"
    by (blast dest: execn_strip_guards_to_execn)
  thus ?thesis
    by (blast intro: execn_to_exec)
qed

lemma exec_strip_to_exec: 
  assumes exec_strip: "strip F \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t" 
  shows "\<exists>t'. \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t' \<and> 
              (isFault t \<longrightarrow> isFault t') \<and> 
              (t' \<in> Fault ` (-F) \<longrightarrow> t'=t) \<and>
              (\<not> isFault t' \<longrightarrow> t'=t)"
proof -
  from exec_strip obtain n where 
    execn_strip: "strip F \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"
    by (auto simp add: exec_iff_execn)
  then obtain t' where
    "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t'"  
    "isFault t \<longrightarrow> isFault t'" "t' \<in> Fault ` (-F) \<longrightarrow> t'=t" "\<not> isFault t' \<longrightarrow> t'=t"
    by (blast dest: execn_strip_to_execn)
  thus ?thesis
    by (blast intro: execn_to_exec)
qed


lemma exec_to_exec_strip_guards:
 assumes exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t" 
 assumes t_not_Fault: "\<not> isFault t"
 shows "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,s\<rangle> \<Rightarrow> t"
proof -
  from exec_c obtain n where "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>t" 
    by (auto simp add: exec_iff_execn)
  from this t_not_Fault
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,s\<rangle> =n\<Rightarrow> t"
    by (rule execn_to_execn_strip_guards )
  thus "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,s\<rangle> \<Rightarrow> t"
    by (rule execn_to_exec)
qed

lemma exec_to_exec_strip_guards':
 assumes exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t" 
 assumes t_not_Fault: "t \<notin> Fault ` F"
 shows "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,s\<rangle> \<Rightarrow> t"
proof -
  from exec_c obtain n where "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>t" 
    by (auto simp add: exec_iff_execn)
  from this t_not_Fault
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,s\<rangle> =n\<Rightarrow> t"
    by (rule execn_to_execn_strip_guards' )
  thus "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,s\<rangle> \<Rightarrow> t"
    by (rule execn_to_exec)
qed

lemma execn_to_execn_strip:
 assumes exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" 
 assumes t_not_Fault: "\<not> isFault t"
 shows "strip F \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"
using exec_c t_not_Fault
proof (induct)
  case (Call p bdy s n  s')
  have bdy: "\<Gamma> p = Some bdy" by fact
  from Call have "strip F \<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal s\<rangle> =n\<Rightarrow> s'"
    by blast
  from execn_to_execn_strip_guards [OF this] Call
  have "strip F \<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F bdy,Normal s\<rangle> =n\<Rightarrow> s'"
    by simp
  moreover from bdy have "(strip F \<Gamma>) p = Some (strip_guards F bdy)"
    by simp
  ultimately
  show ?case
    by (blast intro: execn.intros)
next
  case CallUndefined thus ?case by (auto intro: execn.CallUndefined)
next 
  case (AwaitTrue) thus ?case using execn_to_execn_strip by (metis Semantic.isFaultE SemanticCon.isFault_simps(3) execn.AwaitTrue strip_eq)  
qed (auto intro: execn.intros dest: noFaultn_startD' simp add: not_isFault_iff)

lemma execn_to_execn_strip':
 assumes exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" 
 assumes t_not_Fault: "t \<notin> Fault ` F"
 shows "strip F \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"
using exec_c t_not_Fault
proof (induct)
  case (Call p bdy s n s')
  have bdy: "\<Gamma> p = Some bdy" by fact
  from Call have "strip F \<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal s\<rangle> =n\<Rightarrow> s'"
    by blast
  from execn_to_execn_strip_guards' [OF this] Call
  have "strip F \<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F bdy,Normal s\<rangle> =n\<Rightarrow> s'"
    by simp
  moreover from bdy have "(strip F \<Gamma>) p = Some (strip_guards F bdy)"
    by simp
  ultimately
  show ?case
    by (blast intro: execn.intros)
next
  case CallUndefined thus ?case by (auto intro: execn.CallUndefined)
next
  case (Seq c1 s n s' c2 t)
  show ?case
  proof (cases "isFault s'") 
    case False
    with Seq show ?thesis
      by (auto intro: execn.intros simp add: not_isFault_iff)
  next
    case True
    then obtain f' where s': "s'=Fault f'" by (auto simp add: isFault_def)
    with Seq obtain "t=Fault f'" and "f' \<notin> F"
      by (force dest: execn_Fault_end)
    with Seq s' show ?thesis
      by (auto intro: execn.intros)
  qed
next
  case (WhileTrue b c s n s' t)
  show ?case
  proof (cases "isFault s'") 
    case False
    with WhileTrue show ?thesis
      by (auto intro: execn.intros simp add: not_isFault_iff)
  next
    case True
    then obtain f' where s': "s'=Fault f'" by (auto simp add: isFault_def)
    with WhileTrue obtain "t=Fault f'" and "f' \<notin> F"
      by (force dest: execn_Fault_end)
    with WhileTrue s' show ?thesis
      by (auto intro: execn.intros)
  qed
next 
  case (AwaitTrue) thus ?case by (metis execn.AwaitTrue strip_eq execn_to_execn_strip')
qed (auto intro: execn.intros)

lemma exec_to_exec_strip:
 assumes exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t" 
 assumes t_not_Fault: "\<not> isFault t"
 shows "strip F \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t"
proof -
  from exec_c obtain n where "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>t" 
    by (auto simp add: exec_iff_execn)
  from this t_not_Fault
  have "strip F \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"
    by (rule execn_to_execn_strip)
  thus "strip F \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t"
    by (rule execn_to_exec)
qed

lemma exec_to_exec_strip':
 assumes exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t" 
 assumes t_not_Fault: "t \<notin> Fault ` F"
 shows "strip F \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t"
proof -
  from exec_c obtain n where "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>t" 
    by (auto simp add: exec_iff_execn)
  from this t_not_Fault
  have "strip F \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"
    by (rule execn_to_execn_strip' )
  thus "strip F \<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t"
    by (rule execn_to_exec)
qed

lemma exec_to_exec_strip_guards_Fault:
 assumes exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> Fault f"
 assumes f_notin_F: "f \<notin> F"
 shows"\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,s\<rangle> \<Rightarrow> Fault f"
proof -
  from exec_c obtain n where "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow>Fault f" 
    by (auto simp add: exec_iff_execn)
  from execn_to_execn_strip_guards_Fault [OF this _ f_notin_F]
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,s\<rangle> =n\<Rightarrow> Fault f"
    by simp
  thus "\<Gamma>\<turnstile>\<^sub>p\<langle>strip_guards F c,s\<rangle> \<Rightarrow> Fault f"
    by (rule execn_to_exec)
qed

(* ************************************************************************* *)
subsection {* Lemmas about @{term "c\<^sub>1 \<inter>\<^sub>g c\<^sub>2"} *}
(* ************************************************************************* *)

lemma inter_guards_execn_Normal_noFault: 
  "\<And>c c2 s t n. \<lbrakk>(c1 \<inter>\<^sub>g\<^sub>s c2) = Some c; \<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> t; \<not> isFault t\<rbrakk>
        \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> =n\<Rightarrow> t \<and> \<Gamma>\<turnstile>\<^sub>p\<langle>c2,Normal s\<rangle> =n\<Rightarrow> t"
proof (induct c1)
  case Skip
  have "(Skip \<inter>\<^sub>g\<^sub>s c2) = Some c" by fact
  then obtain c2: "c2=Skip" and c: "c=Skip"
    by (simp add: inter_guards_Skip)
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" by fact
  with c have "t=Normal s"
    by (auto elim: execn_Normal_elim_cases)
  with Skip c2
  show ?case
    by (auto intro: execn.intros)
next
  case (Basic f e)
  have "(Basic f e \<inter>\<^sub>g\<^sub>s c2) = Some c" by fact
  then obtain c2: "c2=Basic f e" and c: "c=Basic f e"
    by (simp add: inter_guards_Basic)
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" by fact
  with c have "t=Normal (f s)"
    by (auto elim: execn_Normal_elim_cases)
  with Basic c2
  show ?case
    by (auto intro: execn.intros)
next
  case (Spec r e)
  have "(Spec r e \<inter>\<^sub>g\<^sub>s c2) = Some c" by fact
  then obtain c2: "c2=Spec r e" and c: "c=Spec r e"
    by (simp add: inter_guards_Spec)
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" by fact
  with c have "\<Gamma>\<turnstile>\<^sub>p\<langle>Spec r e,Normal s\<rangle> =n\<Rightarrow> t" by simp
  from this Spec c2 show ?case
    by (cases) (auto intro: execn.intros)
next
  case (Seq a1 a2)
  have noFault: "\<not> isFault t" by fact
  have "(Seq a1 a2 \<inter>\<^sub>g\<^sub>s c2) = Some c" by fact
  then obtain b1 b2 d1 d2 where
    c2: "c2=Seq b1 b2" and 
    d1: "(a1 \<inter>\<^sub>g\<^sub>s b1) = Some d1" and d2: "(a2 \<inter>\<^sub>g\<^sub>s b2) = Some d2" and
    c: "c=Seq d1 d2"
    by (auto simp add: inter_guards_Seq)
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" by fact
  with c obtain s' where 
    exec_d1: "\<Gamma>\<turnstile>\<^sub>p\<langle>d1,Normal s\<rangle> =n\<Rightarrow> s'" and
    exec_d2: "\<Gamma>\<turnstile>\<^sub>p\<langle>d2,s'\<rangle> =n\<Rightarrow> t"
    by (auto elim: execn_Normal_elim_cases)
  show ?case
  proof (cases s')
    case (Fault f')
    with exec_d2 have "t=Fault f'" 
      by (auto intro: execn_Fault_end)
    with noFault show  ?thesis by simp
  next
    case (Normal s'')
    with d1 exec_d1 Seq.hyps
    obtain 
      "\<Gamma>\<turnstile>\<^sub>p\<langle>a1,Normal s\<rangle> =n\<Rightarrow> Normal s''" and "\<Gamma>\<turnstile>\<^sub>p\<langle>b1,Normal s\<rangle> =n\<Rightarrow> Normal s''"
      by auto
    moreover
    from Normal d2 exec_d2 noFault Seq.hyps
    obtain "\<Gamma>\<turnstile>\<^sub>p\<langle>a2,Normal s''\<rangle> =n\<Rightarrow> t" and "\<Gamma>\<turnstile>\<^sub>p\<langle>b2,Normal s''\<rangle> =n\<Rightarrow> t"
      by auto
    ultimately
    show ?thesis
      using Normal c2 by (auto intro: execn.intros)
  next
    case (Abrupt s'')
    with exec_d2 have "t=Abrupt s''"
      by (auto simp add: execn_Abrupt_end)
    moreover
    from Abrupt d1 exec_d1 Seq.hyps
    obtain "\<Gamma>\<turnstile>\<^sub>p\<langle>a1,Normal s\<rangle> =n\<Rightarrow> Abrupt s''" and "\<Gamma>\<turnstile>\<^sub>p\<langle>b1,Normal s\<rangle> =n\<Rightarrow> Abrupt s''"
      by auto
    moreover
    obtain 
      "\<Gamma>\<turnstile>\<^sub>p\<langle>a2,Abrupt s''\<rangle> =n\<Rightarrow> Abrupt s''" and "\<Gamma>\<turnstile>\<^sub>p\<langle>b2,Abrupt s''\<rangle> =n\<Rightarrow> Abrupt s''"
      by auto
    ultimately
    show ?thesis
      using Abrupt c2 by (auto intro: execn.intros)
  next
    case Stuck
    with exec_d2 have "t=Stuck"
      by (auto simp add: execn_Stuck_end)
    moreover
    from Stuck d1 exec_d1 Seq.hyps
    obtain "\<Gamma>\<turnstile>\<^sub>p\<langle>a1,Normal s\<rangle> =n\<Rightarrow> Stuck" and "\<Gamma>\<turnstile>\<^sub>p\<langle>b1,Normal s\<rangle> =n\<Rightarrow> Stuck"
      by auto
    moreover
    obtain 
      "\<Gamma>\<turnstile>\<^sub>p\<langle>a2,Stuck\<rangle> =n\<Rightarrow> Stuck" and "\<Gamma>\<turnstile>\<^sub>p\<langle>b2,Stuck\<rangle> =n\<Rightarrow> Stuck"
      by auto
    ultimately
    show ?thesis
      using Stuck c2 by (auto intro: execn.intros)
  qed
next
  case (Cond b t1 e1)
  have noFault: "\<not> isFault t" by fact
  have "(Cond b t1 e1 \<inter>\<^sub>g\<^sub>s c2) = Some c" by fact
  then obtain t2 e2 t3 e3 where
    c2: "c2=Cond b t2 e2" and
    t3: "(t1 \<inter>\<^sub>g\<^sub>s t2) = Some t3" and
    e3: "(e1 \<inter>\<^sub>g\<^sub>s e2) = Some e3" and
    c: "c=Cond b t3 e3"
    by (auto simp add: inter_guards_Cond)
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" by fact
  with c have "\<Gamma>\<turnstile>\<^sub>p\<langle>Cond b t3 e3,Normal s\<rangle> =n\<Rightarrow> t"
    by simp
  then show ?case
  proof (cases)
    assume s_in_b: "s\<in>b" 
    assume "\<Gamma>\<turnstile>\<^sub>p\<langle>t3,Normal s\<rangle> =n\<Rightarrow> t"
    with Cond.hyps t3 noFault
    obtain "\<Gamma>\<turnstile>\<^sub>p\<langle>t1,Normal s\<rangle> =n\<Rightarrow> t" "\<Gamma>\<turnstile>\<^sub>p\<langle>t2,Normal s\<rangle> =n\<Rightarrow> t"
      by auto
    with s_in_b c2 show ?thesis
      by (auto intro: execn.intros)
  next
    assume s_notin_b: "s\<notin>b" 
    assume "\<Gamma>\<turnstile>\<^sub>p\<langle>e3,Normal s\<rangle> =n\<Rightarrow> t"
    with Cond.hyps e3 noFault
    obtain "\<Gamma>\<turnstile>\<^sub>p\<langle>e1,Normal s\<rangle> =n\<Rightarrow> t" "\<Gamma>\<turnstile>\<^sub>p\<langle>e2,Normal s\<rangle> =n\<Rightarrow> t"
      by auto
    with s_notin_b c2 show ?thesis
      by (auto intro: execn.intros)
  qed
next
  case (While b bdy1)
  have noFault: "\<not> isFault t" by fact
  have "(While b bdy1 \<inter>\<^sub>g\<^sub>s c2) = Some c" by fact
  then obtain bdy2 bdy where
    c2: "c2=While b bdy2" and
    bdy: "(bdy1 \<inter>\<^sub>g\<^sub>s bdy2) = Some bdy" and
    c: "c=While b bdy"
    by (auto simp add: inter_guards_While)
  have exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" by fact
  {
    fix s t n w w1 w2
    assume exec_w: "\<Gamma>\<turnstile>\<^sub>p\<langle>w,Normal s\<rangle> =n\<Rightarrow> t" 
    assume w: "w=While b bdy"
    assume noFault: "\<not> isFault t"
    from exec_w w noFault
    have "\<Gamma>\<turnstile>\<^sub>p\<langle>While b bdy1,Normal s\<rangle> =n\<Rightarrow> t \<and> 
          \<Gamma>\<turnstile>\<^sub>p\<langle>While b bdy2,Normal s\<rangle> =n\<Rightarrow> t"
    proof (induct)
      prefer 10
      case (WhileTrue s b' bdy' n s' s'')
      have eqs: "While b'  bdy' = While b bdy" by fact
      from WhileTrue have s_in_b: "s \<in> b" by simp
      have noFault_s'': "\<not> isFault s''"  by fact
      from WhileTrue 
      have exec_bdy: "\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal s\<rangle> =n\<Rightarrow> s'" by simp
      from WhileTrue
      have exec_w: "\<Gamma>\<turnstile>\<^sub>p\<langle>While b bdy,s'\<rangle> =n\<Rightarrow> s''" by simp
      show ?case
      proof (cases s')
        case (Fault f)
        with exec_w have "s''=Fault f"
          by (auto intro: execn_Fault_end)
        with noFault_s'' show ?thesis by simp
      next
        case (Normal s''')
        with exec_bdy bdy While.hyps
        obtain "\<Gamma>\<turnstile>\<^sub>p\<langle>bdy1,Normal s\<rangle> =n\<Rightarrow> Normal s'''" 
               "\<Gamma>\<turnstile>\<^sub>p\<langle>bdy2,Normal s\<rangle> =n\<Rightarrow> Normal s'''"
          by auto
        moreover
        from Normal WhileTrue
        obtain 
          "\<Gamma>\<turnstile>\<^sub>p\<langle>While b bdy1,Normal s'''\<rangle> =n\<Rightarrow> s''" 
          "\<Gamma>\<turnstile>\<^sub>p\<langle>While b bdy2,Normal s'''\<rangle> =n\<Rightarrow> s''"
          by simp
        ultimately show ?thesis
          using s_in_b Normal
          by (auto intro: execn.intros)
      next
        case (Abrupt s''')
        with exec_bdy bdy While.hyps
        obtain "\<Gamma>\<turnstile>\<^sub>p\<langle>bdy1,Normal s\<rangle> =n\<Rightarrow> Abrupt s'''" 
               "\<Gamma>\<turnstile>\<^sub>p\<langle>bdy2,Normal s\<rangle> =n\<Rightarrow> Abrupt s'''"
          by auto
        moreover
        from Abrupt WhileTrue
        obtain 
          "\<Gamma>\<turnstile>\<^sub>p\<langle>While b bdy1,Abrupt s'''\<rangle> =n\<Rightarrow> s''" 
          "\<Gamma>\<turnstile>\<^sub>p\<langle>While b bdy2,Abrupt s'''\<rangle> =n\<Rightarrow> s''"
          by simp
        ultimately show ?thesis
          using s_in_b Abrupt
          by (auto intro: execn.intros)
      next
        case Stuck
        with exec_bdy bdy While.hyps
        obtain "\<Gamma>\<turnstile>\<^sub>p\<langle>bdy1,Normal s\<rangle> =n\<Rightarrow> Stuck" 
               "\<Gamma>\<turnstile>\<^sub>p\<langle>bdy2,Normal s\<rangle> =n\<Rightarrow> Stuck"
          by auto
        moreover
        from Stuck WhileTrue
        obtain 
          "\<Gamma>\<turnstile>\<^sub>p\<langle>While b bdy1,Stuck\<rangle> =n\<Rightarrow> s''" 
          "\<Gamma>\<turnstile>\<^sub>p\<langle>While b bdy2,Stuck\<rangle> =n\<Rightarrow> s''"
          by simp
        ultimately show ?thesis
          using s_in_b Stuck
          by (auto intro: execn.intros)
      qed
    next
      case WhileFalse thus ?case by (auto intro: execn.intros)
    qed (simp_all)  
  }
  with this [OF exec_c c noFault] c2
  show ?case
    by auto
next
  case Call thus ?case by (simp add: inter_guards_Call)
next
  case (DynCom f1)  
  have noFault: "\<not> isFault t" by fact
  have "(DynCom f1 \<inter>\<^sub>g\<^sub>s c2) = Some c" by fact
  then obtain f2 f where
    c2: "c2=DynCom f2" and
    f_defined: "\<forall>s. ((f1 s) \<inter>\<^sub>g\<^sub>s (f2 s)) \<noteq> None" and
    c: "c=DynCom (\<lambda>s. the ((f1 s) \<inter>\<^sub>g\<^sub>s (f2 s)))"
    by (auto simp add: inter_guards_DynCom)
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" by fact
  with c have "\<Gamma>\<turnstile>\<^sub>p\<langle>DynCom (\<lambda>s. the ((f1 s) \<inter>\<^sub>g\<^sub>s (f2 s))),Normal s\<rangle> =n\<Rightarrow> t" by simp
  then show ?case
  proof (cases)
    assume exec_f: "\<Gamma>\<turnstile>\<^sub>p\<langle>the (f1 s \<inter>\<^sub>g\<^sub>s f2 s),Normal s\<rangle> =n\<Rightarrow> t"
    from f_defined obtain f where "(f1 s \<inter>\<^sub>g\<^sub>s f2 s) = Some f"
      by auto
    with DynCom.hyps this exec_f c2 noFault
    show ?thesis
      using execn.DynCom by fastforce
  qed
next
  case Guard thus ?case 
    by (fastforce elim: execn_Normal_elim_cases intro: execn.intros 
        simp add: inter_guards_Guard)
next
  case Throw thus ?case
    by (fastforce elim: execn_Normal_elim_cases 
        simp add: inter_guards_Throw)
next
  case (Catch a1 a2)
  have noFault: "\<not> isFault t" by fact
  have "(Catch a1 a2 \<inter>\<^sub>g\<^sub>s c2) = Some c" by fact
  then obtain b1 b2 d1 d2 where
    c2: "c2=Catch b1 b2" and 
    d1: "(a1 \<inter>\<^sub>g\<^sub>s b1) = Some d1" and d2: "(a2 \<inter>\<^sub>g\<^sub>s b2) = Some d2" and
    c: "c=Catch d1 d2"
    by (auto simp add: inter_guards_Catch)
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" by fact
  with c have "\<Gamma>\<turnstile>\<^sub>p\<langle>Catch d1 d2,Normal s\<rangle> =n\<Rightarrow> t" by simp
  then show ?case
  proof (cases)
    fix s'
    assume "\<Gamma>\<turnstile>\<^sub>p\<langle>d1,Normal s\<rangle> =n\<Rightarrow> Abrupt s'"
    with d1 Catch.hyps
    obtain "\<Gamma>\<turnstile>\<^sub>p\<langle>a1,Normal s\<rangle> =n\<Rightarrow> Abrupt s'" and "\<Gamma>\<turnstile>\<^sub>p\<langle>b1,Normal s\<rangle> =n\<Rightarrow> Abrupt s'"
      by auto
    moreover
    assume "\<Gamma>\<turnstile>\<^sub>p\<langle>d2,Normal s'\<rangle> =n\<Rightarrow> t"
    with d2 Catch.hyps noFault
    obtain "\<Gamma>\<turnstile>\<^sub>p\<langle>a2,Normal s'\<rangle> =n\<Rightarrow> t" and "\<Gamma>\<turnstile>\<^sub>p\<langle>b2,Normal s'\<rangle> =n\<Rightarrow> t"
      by auto
    ultimately
    show ?thesis
      using c2 by (auto intro: execn.intros)
  next
    assume "\<not> isAbr t"
    moreover
    assume "\<Gamma>\<turnstile>\<^sub>p\<langle>d1,Normal s\<rangle> =n\<Rightarrow> t"
    with d1 Catch.hyps noFault
    obtain "\<Gamma>\<turnstile>\<^sub>p\<langle>a1,Normal s\<rangle> =n\<Rightarrow> t" and "\<Gamma>\<turnstile>\<^sub>p\<langle>b1,Normal s\<rangle> =n\<Rightarrow> t"
      by auto
    ultimately
    show ?thesis
      using c2 by (auto intro: execn.intros)
  qed
next
 case (Await b bdy1 e)  
  have noFault: "\<not> isFault t" by fact
  have "(Await b bdy1 e \<inter>\<^sub>g\<^sub>s c2) = Some c" by fact  
  then obtain bdy2 bdy where
    c2: "c2=Await b bdy2 e" and
    bdy: "(bdy1 \<inter>\<^sub>g bdy2) = Some bdy" and
    c: "c=Await b bdy e"
    by (auto simp add: inter_guards_Await)
  have exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" by fact
  then have "\<Gamma>\<turnstile>\<^sub>p\<langle>Await b bdy1 e,Normal s\<rangle> =n\<Rightarrow> t"
    by (metis Semantic.isFaultE SemanticCon.execn_Normal_elim_cases(11) SemanticCon.isFault_simps(3) bdy c execn.AwaitFalse execn.AwaitTrue inter_guards_execn_Normal_noFault noFault)
  thus ?case using exec_c
    by (metis Semantic.isFaultE SemanticCon.execn_Normal_elim_cases(11) SemanticCon.isFault_simps(3) bdy c execn.AwaitFalse c2 execn.AwaitTrue inter_guards_execn_Normal_noFault noFault)
qed


lemma inter_guards_execn_noFault: 
  assumes c: "(c1 \<inter>\<^sub>g\<^sub>s c2) = Some c"
  assumes exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"
  assumes noFault: "\<not> isFault t" 
  shows "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,s\<rangle> =n\<Rightarrow> t \<and> \<Gamma>\<turnstile>\<^sub>p\<langle>c2,s\<rangle> =n\<Rightarrow> t"
proof (cases s) 
  case (Fault f)
  with exec_c have "t = Fault f"
    by (auto intro: execn_Fault_end)
    with noFault show ?thesis
    by simp 
next
  case (Abrupt s')
  with exec_c have "t=Abrupt s'"
    by (simp add: execn_Abrupt_end)
  with Abrupt show ?thesis by auto
next
  case Stuck
  with exec_c have "t=Stuck"
    by (simp add: execn_Stuck_end)
  with Stuck show ?thesis by auto
next
  case (Normal s')
  with exec_c noFault inter_guards_execn_Normal_noFault [OF c]
  show ?thesis
    by blast
qed

lemma inter_guards_exec_noFault: 
  assumes c: "(c1 \<inter>\<^sub>g\<^sub>s c2) = Some c"
  assumes exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t"
  assumes noFault: "\<not> isFault t" 
  shows "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,s\<rangle> \<Rightarrow> t \<and> \<Gamma>\<turnstile>\<^sub>p\<langle>c2,s\<rangle> \<Rightarrow> t"
proof -
  from exec_c obtain n where "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"
    by (auto simp add: exec_iff_execn)
  from c this noFault
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,s\<rangle> =n\<Rightarrow> t \<and> \<Gamma>\<turnstile>\<^sub>p\<langle>c2,s\<rangle> =n\<Rightarrow> t"
    by (rule inter_guards_execn_noFault)
  thus ?thesis
    by (auto intro: execn_to_exec)
qed


lemma inter_guards_execn_Normal_Fault: 
  "\<And>c c2 s n. \<lbrakk>(c1 \<inter>\<^sub>g\<^sub>s c2) = Some c; \<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> Fault f\<rbrakk>
        \<Longrightarrow> (\<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> =n\<Rightarrow> Fault f \<or> \<Gamma>\<turnstile>\<^sub>p\<langle>c2,Normal s\<rangle> =n\<Rightarrow> Fault f)"
proof (induct c1)
  case Skip thus ?case by (fastforce simp add: inter_guards_Skip)
next
  case (Basic f) thus ?case by (fastforce simp add: inter_guards_Basic)
next
  case (Spec r) thus ?case by (fastforce simp add: inter_guards_Spec)
next
  case (Seq a1 a2)
  have "(Seq a1 a2 \<inter>\<^sub>g\<^sub>s c2) = Some c" by fact
  then obtain b1 b2 d1 d2 where
    c2: "c2=Seq b1 b2" and 
    d1: "(a1 \<inter>\<^sub>g\<^sub>s b1) = Some d1" and d2: "(a2 \<inter>\<^sub>g\<^sub>s b2) = Some d2" and
    c: "c=Seq d1 d2"
    by (auto simp add: inter_guards_Seq)
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> Fault f" by fact
  with c obtain s' where 
    exec_d1: "\<Gamma>\<turnstile>\<^sub>p\<langle>d1,Normal s\<rangle> =n\<Rightarrow> s'" and
    exec_d2: "\<Gamma>\<turnstile>\<^sub>p\<langle>d2,s'\<rangle> =n\<Rightarrow> Fault f"
    by (auto elim: execn_Normal_elim_cases)
  show ?case
  proof (cases s')
    case (Fault f')
    with exec_d2 have "f'=f"
      by (auto dest: execn_Fault_end)
    with Fault d1 exec_d1 
    have "\<Gamma>\<turnstile>\<^sub>p\<langle>a1,Normal s\<rangle> =n\<Rightarrow> Fault f \<or> \<Gamma>\<turnstile>\<^sub>p\<langle>b1,Normal s\<rangle> =n\<Rightarrow> Fault f" 
      by (auto dest: Seq.hyps)
    thus ?thesis
    proof (cases rule: disjE [consumes 1])
      assume "\<Gamma>\<turnstile>\<^sub>p\<langle>a1,Normal s\<rangle> =n\<Rightarrow> Fault f" 
      hence "\<Gamma>\<turnstile>\<^sub>p\<langle>Seq a1 a2,Normal s\<rangle> =n\<Rightarrow> Fault f"
        by (auto intro: execn.intros)
      thus ?thesis
        by simp
    next
      assume "\<Gamma>\<turnstile>\<^sub>p\<langle>b1,Normal s\<rangle> =n\<Rightarrow> Fault f" 
      hence "\<Gamma>\<turnstile>\<^sub>p\<langle>Seq b1 b2,Normal s\<rangle> =n\<Rightarrow> Fault f"
        by (auto intro: execn.intros)
      with c2 show ?thesis
        by simp
    qed
  next
    case Abrupt with exec_d2 show ?thesis by (auto dest: execn_Abrupt_end)
  next
    case Stuck with exec_d2 show ?thesis by (auto dest: execn_Stuck_end)
  next
    case (Normal s'') 
    with inter_guards_execn_noFault [OF d1 exec_d1] obtain
      exec_a1: "\<Gamma>\<turnstile>\<^sub>p\<langle>a1,Normal s\<rangle> =n\<Rightarrow> Normal s''" and
      exec_b1: "\<Gamma>\<turnstile>\<^sub>p\<langle>b1,Normal s\<rangle> =n\<Rightarrow> Normal s''"
      by simp
    moreover from d2 exec_d2 Normal 
    have "\<Gamma>\<turnstile>\<^sub>p\<langle>a2,Normal s''\<rangle> =n\<Rightarrow> Fault f \<or> \<Gamma>\<turnstile>\<^sub>p\<langle>b2,Normal s''\<rangle> =n\<Rightarrow> Fault f" 
      by (auto dest: Seq.hyps)
    ultimately show ?thesis
      using c2 by (auto intro: execn.intros)
  qed
next
  case (Cond b t1 e1)
  have "(Cond b t1 e1 \<inter>\<^sub>g\<^sub>s c2) = Some c" by fact
  then obtain t2 e2 t e where
    c2: "c2=Cond b t2 e2" and
    t: "(t1 \<inter>\<^sub>g\<^sub>s t2) = Some t" and
    e: "(e1 \<inter>\<^sub>g\<^sub>s e2) = Some e" and
    c: "c=Cond b t e"
    by (auto simp add: inter_guards_Cond)
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> Fault f" by fact
  with c have "\<Gamma>\<turnstile>\<^sub>p\<langle>Cond b t e,Normal s\<rangle> =n\<Rightarrow> Fault f" by simp
  thus ?case
  proof (cases)
    assume "s \<in> b"
    moreover assume "\<Gamma>\<turnstile>\<^sub>p\<langle>t,Normal s\<rangle> =n\<Rightarrow> Fault f"
    with t have "\<Gamma>\<turnstile>\<^sub>p\<langle>t1,Normal s\<rangle> =n\<Rightarrow> Fault f \<or> \<Gamma>\<turnstile>\<^sub>p\<langle>t2,Normal s\<rangle> =n\<Rightarrow> Fault f"
      by (auto dest: Cond.hyps)
    ultimately show ?thesis using c2 c by (fastforce intro: execn.intros)
  next
    assume "s \<notin> b"
    moreover assume "\<Gamma>\<turnstile>\<^sub>p\<langle>e,Normal s\<rangle> =n\<Rightarrow> Fault f"
    with e have "\<Gamma>\<turnstile>\<^sub>p\<langle>e1,Normal s\<rangle> =n\<Rightarrow> Fault f \<or> \<Gamma>\<turnstile>\<^sub>p\<langle>e2,Normal s\<rangle> =n\<Rightarrow> Fault f"
      by (auto dest: Cond.hyps)
    ultimately show ?thesis using c2 c by (fastforce intro: execn.intros)
  qed
next
  case (While b bdy1)
  have "(While b bdy1 \<inter>\<^sub>g\<^sub>s c2) = Some c" by fact
  then obtain bdy2 bdy where
    c2: "c2=While b bdy2" and
    bdy: "(bdy1 \<inter>\<^sub>g\<^sub>s bdy2) = Some bdy" and
    c: "c=While b bdy"
    by (auto simp add: inter_guards_While)
  have exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> Fault f" by fact
  {
    fix s t n w w1 w2 
    assume exec_w: "\<Gamma>\<turnstile>\<^sub>p\<langle>w,Normal s\<rangle> =n\<Rightarrow> t" 
    assume w: "w=While b bdy"
    assume Fault: "t=Fault f"
    from exec_w w Fault
    have "\<Gamma>\<turnstile>\<^sub>p\<langle>While b bdy1,Normal s\<rangle> =n\<Rightarrow> Fault f\<or>  
          \<Gamma>\<turnstile>\<^sub>p\<langle>While b bdy2,Normal s\<rangle> =n\<Rightarrow> Fault f"
    proof (induct)
      case (WhileTrue s b' bdy' n  s' s'')
      have eqs: "While b' bdy' = While b bdy" by fact
      from WhileTrue have s_in_b: "s \<in> b" by simp
      have Fault_s'': "s''=Fault f"  by fact
      from WhileTrue 
      have exec_bdy: "\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal s\<rangle> =n\<Rightarrow> s'" by simp
      from WhileTrue
      have exec_w: "\<Gamma>\<turnstile>\<^sub>p\<langle>While b bdy,s'\<rangle> =n\<Rightarrow> s''" by simp
      show ?case
      proof (cases s')
        case (Fault f')
        with exec_w Fault_s'' have "f'=f"
          by (auto dest: execn_Fault_end)
        with Fault exec_bdy bdy While.hyps
        have "\<Gamma>\<turnstile>\<^sub>p\<langle>bdy1,Normal s\<rangle> =n\<Rightarrow> Fault f \<or> \<Gamma>\<turnstile>\<^sub>p\<langle>bdy2,Normal s\<rangle> =n\<Rightarrow> Fault f"
          by auto
        with s_in_b show ?thesis
          by (fastforce intro: execn.intros)
      next
        case (Normal s''')
        with inter_guards_execn_noFault [OF bdy exec_bdy]
        obtain "\<Gamma>\<turnstile>\<^sub>p\<langle>bdy1,Normal s\<rangle> =n\<Rightarrow> Normal s'''" 
               "\<Gamma>\<turnstile>\<^sub>p\<langle>bdy2,Normal s\<rangle> =n\<Rightarrow> Normal s'''"
          by auto
        moreover
        from Normal WhileTrue
        have "\<Gamma>\<turnstile>\<^sub>p\<langle>While b bdy1,Normal s'''\<rangle> =n\<Rightarrow> Fault f \<or>
              \<Gamma>\<turnstile>\<^sub>p\<langle>While b bdy2,Normal s'''\<rangle> =n\<Rightarrow> Fault f"
          by simp
        ultimately show ?thesis
          using s_in_b by (fastforce intro: execn.intros)
      next
        case (Abrupt s''')
        with exec_w Fault_s'' show ?thesis by (fastforce dest: execn_Abrupt_end)
      next
        case Stuck
        with exec_w Fault_s'' show ?thesis by (fastforce dest: execn_Stuck_end)
      qed
    next
      case WhileFalse thus ?case by (auto intro: execn.intros)
    qed (simp_all)  
  }
  with this [OF exec_c c] c2
  show ?case
    by auto
next
  case Call thus ?case by (fastforce simp add: inter_guards_Call)
next
  case (DynCom f1)
  have "(DynCom f1 \<inter>\<^sub>g\<^sub>s c2) = Some c" by fact
  then obtain f2  where
    c2: "c2=DynCom f2" and
    F_defined: "\<forall>s. ((f1 s) \<inter>\<^sub>g\<^sub>s (f2 s)) \<noteq> None" and
    c: "c=DynCom (\<lambda>s. the ((f1 s) \<inter>\<^sub>g\<^sub>s (f2 s)))"
    by (auto simp add: inter_guards_DynCom)
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> Fault f" by fact
  with c have "\<Gamma>\<turnstile>\<^sub>p\<langle>DynCom (\<lambda>s. the ((f1 s) \<inter>\<^sub>g\<^sub>s (f2 s))),Normal s\<rangle> =n\<Rightarrow> Fault f" by simp
  then show ?case
  proof (cases)
    assume exec_F: "\<Gamma>\<turnstile>\<^sub>p\<langle>the (f1 s \<inter>\<^sub>g\<^sub>s f2 s),Normal s\<rangle> =n\<Rightarrow> Fault f"
    from F_defined obtain F where "(f1 s \<inter>\<^sub>g\<^sub>s f2 s) = Some F"
      by auto
    with DynCom.hyps this exec_F c2 
    show ?thesis
      by (fastforce intro: execn.intros)
  qed
next
  case (Guard m g1 bdy1)
  have "(Guard m g1 bdy1 \<inter>\<^sub>g\<^sub>s c2) = Some c" by fact
  then obtain g2 bdy2 bdy where
    c2: "c2=Guard m g2 bdy2" and
    bdy: "(bdy1 \<inter>\<^sub>g\<^sub>s bdy2) = Some bdy" and
    c: "c=Guard m (g1 \<inter> g2) bdy"
    by (auto simp add: inter_guards_Guard)
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> Fault f" by fact
  with c have "\<Gamma>\<turnstile>\<^sub>p\<langle>Guard m (g1 \<inter> g2) bdy,Normal s\<rangle> =n\<Rightarrow> Fault f"
    by simp
  thus ?case
  proof (cases)
    assume f_m: "Fault f = Fault m"
    assume "s \<notin> g1 \<inter> g2"
    hence "s\<notin>g1 \<or> s\<notin>g2"
      by blast
    with c2 f_m show ?thesis
      by (auto intro: execn.intros)
  next
    assume "s \<in> g1 \<inter> g2"
    moreover
    assume "\<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal s\<rangle> =n\<Rightarrow> Fault f"
    with bdy have "\<Gamma>\<turnstile>\<^sub>p\<langle>bdy1,Normal s\<rangle> =n\<Rightarrow> Fault f \<or> \<Gamma>\<turnstile>\<^sub>p\<langle>bdy2,Normal s\<rangle> =n\<Rightarrow> Fault f"
      by (rule Guard.hyps)
    ultimately show ?thesis
      using c2
      by (auto intro: execn.intros)
  qed
next
  case Throw thus ?case by (fastforce simp add: inter_guards_Throw)
next
  case (Catch a1 a2)
  have "(Catch a1 a2 \<inter>\<^sub>g\<^sub>s c2) = Some c" by fact
  then obtain b1 b2 d1 d2 where
    c2: "c2=Catch b1 b2" and 
    d1: "(a1 \<inter>\<^sub>g\<^sub>s b1) = Some d1" and d2: "(a2 \<inter>\<^sub>g\<^sub>s b2) = Some d2" and
    c: "c=Catch d1 d2"
    by (auto simp add: inter_guards_Catch)
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> Fault f" by fact
  with c have "\<Gamma>\<turnstile>\<^sub>p\<langle>Catch d1 d2,Normal s\<rangle> =n\<Rightarrow> Fault f" by simp
  thus ?case
  proof (cases)
    fix s'
    assume "\<Gamma>\<turnstile>\<^sub>p\<langle>d1,Normal s\<rangle> =n\<Rightarrow> Abrupt s'"
    from inter_guards_execn_noFault [OF d1 this] obtain
      exec_a1: "\<Gamma>\<turnstile>\<^sub>p\<langle>a1,Normal s\<rangle> =n\<Rightarrow> Abrupt s'" and
      exec_b1: "\<Gamma>\<turnstile>\<^sub>p\<langle>b1,Normal s\<rangle> =n\<Rightarrow> Abrupt s'"
      by simp
    moreover assume  "\<Gamma>\<turnstile>\<^sub>p\<langle>d2,Normal s'\<rangle> =n\<Rightarrow> Fault f"
    with d2 
    have "\<Gamma>\<turnstile>\<^sub>p\<langle>a2,Normal s'\<rangle> =n\<Rightarrow> Fault f \<or> \<Gamma>\<turnstile>\<^sub>p\<langle>b2,Normal s'\<rangle> =n\<Rightarrow> Fault f" 
      by (auto dest: Catch.hyps)
    ultimately show ?thesis
      using c2 by (fastforce intro: execn.intros)
  next
    assume "\<Gamma>\<turnstile>\<^sub>p\<langle>d1,Normal s\<rangle> =n\<Rightarrow> Fault f" 
    with d1 have "\<Gamma>\<turnstile>\<^sub>p\<langle>a1,Normal s\<rangle> =n\<Rightarrow> Fault f \<or> \<Gamma>\<turnstile>\<^sub>p\<langle>b1,Normal s\<rangle> =n\<Rightarrow> Fault f" 
      by (auto dest: Catch.hyps)
    with c2 show ?thesis
      by (fastforce intro: execn.intros)
  qed
next 
case (Await b bdy1 e) 
  have "(Await b bdy1 e \<inter>\<^sub>g\<^sub>s c2) = Some c" by fact
  then obtain bdy2 bdy where
    c2: "c2=Await b bdy2 e" and
    bdy: "(bdy1 \<inter>\<^sub>g bdy2) = Some bdy" and
    c: "c=Await b bdy e"
    by (auto simp add: inter_guards_Await)
  have exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> =n\<Rightarrow> Fault f" by fact
  {
    fix s t n w 
    assume exec_w: "\<Gamma>\<turnstile>\<^sub>p\<langle>w,Normal s\<rangle> =n\<Rightarrow> t" 
    assume w: "w=Await b bdy e"
    assume Fault: "t=Fault f"
    from exec_w w Fault
    have "\<Gamma>\<turnstile>\<^sub>p\<langle>Await b bdy1 e,Normal s\<rangle> =n\<Rightarrow> Fault f\<or>  
          \<Gamma>\<turnstile>\<^sub>p\<langle>Await b bdy2 e,Normal s\<rangle> =n\<Rightarrow> Fault f"
    using   SemanticCon.execn_Normal_elim_cases(11) bdy execn.AwaitTrue inter_guards_execn_Fault xstate.distinct(3)
   by (metis)
            
  }
  with this [OF exec_c c] c2
  show ?case
    by auto 
qed



lemma inter_guards_execn_Fault: 
  assumes c: "(c1 \<inter>\<^sub>g\<^sub>s c2) = Some c"
  assumes exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> Fault f"
  shows "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,s\<rangle> =n\<Rightarrow> Fault f \<or> \<Gamma>\<turnstile>\<^sub>p\<langle>c2,s\<rangle> =n\<Rightarrow> Fault f"
proof (cases s) 
  case (Fault f)
  with exec_c show ?thesis
    by (auto dest: execn_Fault_end)
next
  case (Abrupt s')
  with exec_c show ?thesis 
    by (fastforce dest: execn_Abrupt_end)
next
  case Stuck
  with exec_c show ?thesis 
    by (fastforce dest: execn_Stuck_end)
next
  case (Normal s')
  with exec_c inter_guards_execn_Normal_Fault [OF c]
  show ?thesis
    by blast
qed

lemma inter_guards_exec_Fault: 
  assumes c: "(c1 \<inter>\<^sub>g\<^sub>s c2) = Some c"
  assumes exec_c: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> Fault f" 
  shows "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,s\<rangle> \<Rightarrow> Fault f \<or> \<Gamma>\<turnstile>\<^sub>p\<langle>c2,s\<rangle> \<Rightarrow> Fault f"
proof -
  from exec_c obtain n where "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> Fault f"
    by (auto simp add: exec_iff_execn)
  from c this 
  have "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,s\<rangle> =n\<Rightarrow> Fault f \<or> \<Gamma>\<turnstile>\<^sub>p\<langle>c2,s\<rangle> =n\<Rightarrow> Fault f"
    by (rule inter_guards_execn_Fault)
  thus ?thesis
    by (auto intro: execn_to_exec)
qed


(* ************************************************************************* *)
subsection "Restriction of Procedure Environment"
(* ************************************************************************* *)

lemma restrict_SomeD: "(m|\<^bsub>A\<^esub>) x = Some y \<Longrightarrow> m x = Some y"
  by (auto simp add: restrict_map_def split: if_split_asm)

(* FIXME: To Map *)
lemma restrict_dom_same [simp]: "m|\<^bsub>dom m\<^esub> = m"
  apply (rule ext)
  apply (clarsimp simp add: restrict_map_def)
  apply (simp only: not_None_eq [symmetric])
  apply rule
  apply (drule sym)
  apply blast
  done

lemma restrict_in_dom: "x \<in> A \<Longrightarrow> (m|\<^bsub>A\<^esub>) x = m x"
  by (auto simp add: restrict_map_def)


lemma restrict_eq: "(\<Gamma>|\<^bsub>A\<^esub>)\<^sub>\<not>\<^sub>a = (\<Gamma>\<^sub>\<not>\<^sub>a)|\<^bsub>A\<^esub>"
unfolding no_await_body_def
apply rule
apply (split option.split)
apply auto
apply (auto simp add:restrict_map_def)
by (meson option.distinct(1))

lemma exec_restrict_to_exec:
  assumes exec_restrict: "\<Gamma>|\<^bsub>A\<^esub>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t" 
  assumes notStuck: "t\<noteq>Stuck"
  shows "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t"
using exec_restrict notStuck
proof (induct)
  case (AwaitTrue s b \<Gamma>\<^sub>p ca t) 
  have "\<Gamma>\<^sub>\<not>\<^sub>a|\<^bsub>A\<^esub> = \<Gamma>\<^sub>p"
    by (simp add: AwaitTrue.hyps(2) restrict_eq)
  hence "\<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>ca,Normal s\<rangle> \<Rightarrow> t"
    using AwaitTrue.hyps(3) AwaitTrue.prems exec_restrict_to_exec by blast
  thus ?case
    by (simp add: AwaitTrue.hyps(1) exec.AwaitTrue)
qed (auto intro: exec.intros dest: restrict_SomeD Stuck_end)



lemma execn_restrict_to_execn:
  assumes exec_restrict: "\<Gamma>|\<^bsub>A\<^esub>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t" 
  assumes notStuck: "t\<noteq>Stuck"
  shows "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"
using exec_restrict notStuck
proof (induct)
 case (AwaitTrue s b \<Gamma>\<^sub>p ca n t) 
  have "\<Gamma>\<^sub>\<not>\<^sub>a|\<^bsub>A\<^esub> = \<Gamma>\<^sub>p"
    by (simp add: AwaitTrue.hyps(2) restrict_eq)
  hence "\<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>ca,Normal s\<rangle> =n\<Rightarrow> t"
    using AwaitTrue.hyps(3) AwaitTrue.prems execn_restrict_to_execn by blast
  thus ?case
    by (simp add: AwaitTrue.hyps(1) execn.AwaitTrue)
qed(auto intro: execn.intros dest: restrict_SomeD execn_Stuck_end)

lemma restrict_NoneD: "m x = None \<Longrightarrow>  (m|\<^bsub>A\<^esub>) x = None"
  by (auto simp add: restrict_map_def split: if_split_asm)

lemma execn_to_execn_restrict:
  assumes execn: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"
  shows "\<exists>t'. \<Gamma>|\<^bsub>P\<^esub>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t' \<and> (t=Stuck \<longrightarrow> t'=Stuck) \<and> 
                (\<forall>f. t=Fault f \<longrightarrow> t'\<in>{Fault f,Stuck}) \<and> (t'\<noteq>Stuck \<longrightarrow> t'=t)"
using execn
proof (induct)
  case Skip show ?case by (blast intro: execn.Skip)
next
  case Guard thus ?case by (auto intro: execn.Guard)
next
  case GuardFault thus ?case by (auto intro: execn.GuardFault)
next
  case FaultProp thus ?case by (auto intro: execn.FaultProp)
next
  case Basic thus ?case by (auto intro: execn.Basic)
next
  case Spec thus ?case by (auto intro: execn.Spec)
next
  case SpecStuck thus ?case by (auto intro: execn.SpecStuck)
next
  case Seq thus ?case by (metis insertCI execn.Seq StuckProp)
next
  case CondTrue thus ?case by (auto intro: execn.CondTrue)
next
  case CondFalse thus ?case by (auto intro: execn.CondFalse)
next
  case WhileTrue thus ?case by (metis insertCI execn.WhileTrue StuckProp)
next
  case WhileFalse thus ?case by (auto intro: execn.WhileFalse)
next
  case (Call p bdy n s s')
  have "\<Gamma> p = Some bdy" by fact
  show ?case
  proof (cases "p \<in> P")
    case True 
    with Call have "(\<Gamma>|\<^bsub>P\<^esub>) p = Some bdy"
      by (simp)
    with Call show ?thesis
      by (auto intro: execn.intros)
  next
    case False
    hence "(\<Gamma>|\<^bsub>P\<^esub>) p = None" by simp
    thus ?thesis
      by (auto intro: execn.CallUndefined)
  qed
next
  case (CallUndefined p n s)
  have "\<Gamma> p = None" by fact
  hence "(\<Gamma>|\<^bsub>P\<^esub>) p = None" by (rule restrict_NoneD)
  thus ?case by (auto intro: execn.CallUndefined)
next
  case StuckProp thus ?case by (auto intro: execn.StuckProp)
next  
  case DynCom thus ?case by (auto intro: execn.DynCom)
next
  case Throw thus ?case by (auto intro: execn.Throw)
next
  case AbruptProp thus ?case by (auto intro: execn.AbruptProp)
next
  case (CatchMatch c1 s n s' c2 s'') 
  from CatchMatch.hyps
  obtain t' t'' where
    exec_res_c1: "\<Gamma>|\<^bsub>P\<^esub>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> =n\<Rightarrow> t'" and
    t'_notStuck: "t' \<noteq> Stuck \<longrightarrow> t' = Abrupt s'" and
    exec_res_c2: "\<Gamma>|\<^bsub>P\<^esub>\<turnstile>\<^sub>p\<langle>c2,Normal s'\<rangle> =n\<Rightarrow> t''" and
    s''_Stuck: "s'' = Stuck \<longrightarrow> t'' = Stuck" and
    s''_Fault: "\<forall>f. s'' = Fault f \<longrightarrow> t'' \<in> {Fault f, Stuck}" and 
    t''_notStuck: "t'' \<noteq> Stuck \<longrightarrow> t'' = s''"
    by auto
  show ?case
  proof (cases "t'=Stuck")
    case True
    with exec_res_c1 
    have "\<Gamma>|\<^bsub>P\<^esub>\<turnstile>\<^sub>p\<langle>Catch c1 c2,Normal s\<rangle> =n\<Rightarrow> Stuck"
      by (auto intro: execn.CatchMiss)
    thus ?thesis
      by auto
  next
    case False
    with t'_notStuck have "t'= Abrupt s'"
      by simp
    with exec_res_c1 exec_res_c2
    have "\<Gamma>|\<^bsub>P\<^esub>\<turnstile>\<^sub>p\<langle>Catch c1 c2,Normal s\<rangle> =n\<Rightarrow> t''"
      by (auto intro: execn.CatchMatch)
    with s''_Stuck s''_Fault t''_notStuck
    show ?thesis
      by blast
  qed
next
  case (CatchMiss c1 s n w c2) 
  have exec_c1: "\<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> =n\<Rightarrow> w" by fact
  from CatchMiss.hyps obtain w' where
    exec_c1': "\<Gamma>|\<^bsub>P\<^esub>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> =n\<Rightarrow> w'" and
    w_Stuck: "w = Stuck \<longrightarrow> w' = Stuck" and
    w_Fault: "\<forall>f. w = Fault f \<longrightarrow> w' \<in> {Fault f, Stuck}" and
    w'_noStuck: "w' \<noteq> Stuck \<longrightarrow> w' = w"
    by auto
  have noAbr_w: "\<not> isAbr w" by fact
  show ?case
  proof (cases w')
    case (Normal s')
    with w'_noStuck have "w'=w"
      by simp
    with exec_c1' Normal w_Stuck w_Fault w'_noStuck
    show ?thesis
      by (fastforce intro: execn.CatchMiss)
  next
    case (Abrupt s')
    with w'_noStuck have "w'=w"
      by simp
    with noAbr_w Abrupt show ?thesis by simp
  next
    case (Fault f)
    with w'_noStuck have "w'=w"
      by simp
    with exec_c1' Fault w_Stuck w_Fault w'_noStuck
    show ?thesis
      by (fastforce intro: execn.CatchMiss)
  next
    case Stuck
    with exec_c1' w_Stuck w_Fault w'_noStuck
    show ?thesis
      by (fastforce intro: execn.CatchMiss)
  qed 
next
  case (AwaitTrue s b \<Gamma>\<^sub>p c n t)
   have "\<Gamma>\<^sub>\<not>\<^sub>a|\<^bsub>P\<^esub> = (\<Gamma>|\<^bsub>P\<^esub>)\<^sub>\<not>\<^sub>a"
    by (simp add: AwaitTrue.hyps(2) restrict_eq)
    thus ?case using execn_to_execn_restrict  by (metis (full_types) AwaitTrue.hyps(1) AwaitTrue.hyps(2) AwaitTrue.hyps(3) execn.AwaitTrue)
next
  case (AwaitFalse s b) thus ?case by (fastforce intro: execn.AwaitFalse)
qed


lemma exec_to_exec_restrict: 
  assumes exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t" 
  shows "\<exists>t'. \<Gamma>|\<^bsub>P\<^esub>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t' \<and> (t=Stuck \<longrightarrow> t'=Stuck) \<and> 
                (\<forall>f. t=Fault f\<longrightarrow> t'\<in>{Fault f,Stuck}) \<and> (t'\<noteq>Stuck \<longrightarrow> t'=t)"
proof -
  from exec obtain n where 
    execn_strip: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"
    by (auto simp add: exec_iff_execn)
  from execn_to_execn_restrict [where P=P,OF this]
  obtain t' where
    "\<Gamma>|\<^bsub>P\<^esub>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t'"  
    "t=Stuck \<longrightarrow> t'=Stuck" "\<forall>f. t=Fault f\<longrightarrow> t'\<in>{Fault f,Stuck}" "t'\<noteq>Stuck \<longrightarrow> t'=t"
    by blast
  thus ?thesis
    by (blast intro: execn_to_exec)
qed

lemma notStuck_GuardD: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>Guard m g c,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}; s \<in> g\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}"
  by (auto simp add: final_notin_def dest: exec.Guard )

lemma notStuck_SeqD1: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>Seq c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}"
  by (auto simp add: final_notin_def dest: exec.Seq )


lemma notStuck_SeqD2: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>Seq c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}; \<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> \<Rightarrow>s'\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c2,s'\<rangle> \<Rightarrow>\<notin>{Stuck}"
  by (auto simp add: final_notin_def dest: exec.Seq )

lemma notStuck_SeqD: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>Seq c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}\<rbrakk> \<Longrightarrow> 
     \<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck} \<and> (\<forall>s'. \<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> \<Rightarrow>s' \<longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c2,s'\<rangle> \<Rightarrow>\<notin>{Stuck})"
  by (auto simp add: final_notin_def dest: exec.Seq )

lemma notStuck_CondTrueD: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>Cond b c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}; s \<in> b\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}"
  by (auto simp add: final_notin_def dest: exec.CondTrue)

lemma notStuck_CondFalseD: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>Cond b c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}; s \<notin> b\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c2,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}"
  by (auto simp add: final_notin_def dest: exec.CondFalse)

lemma notStuck_WhileTrueD1: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}; s \<in> b\<rbrakk> 
   \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}"
  by (auto simp add: final_notin_def dest: exec.WhileTrue)

lemma notStuck_WhileTrueD2: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>While b c,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}; \<Gamma>\<turnstile>\<^sub>p\<langle>c,Normal s\<rangle> \<Rightarrow>s'; s \<in> b\<rbrakk> 
   \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>While b c,s'\<rangle> \<Rightarrow>\<notin>{Stuck}"
  by (auto simp add: final_notin_def dest: exec.WhileTrue)

lemma notStuck_AwaitTrueD1: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>Await b c e,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}; s \<in> b\<rbrakk> 
   \<Longrightarrow> \<exists>\<Gamma>1. \<Gamma>1\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}"
  by (meson Semantic.noStuckI' SemanticCon.noStuck_def' exec.AwaitTrue)
    

lemma notStuck_AwaitTrueD2: 
   "\<lbrakk>\<Gamma>1\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}; s \<in> b; \<Gamma>1=\<Gamma>\<^sub>\<not>\<^sub>a\<rbrakk> 
   \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>Await b c e,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}"    
  unfolding Semantic.final_notin_def final_notin_def
   by (meson SemanticCon.exec_Normal_elim_cases(11)) 


lemma notStuck_CallD: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>Call p ,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}; \<Gamma> p = Some bdy\<rbrakk> 
   \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>bdy,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}"
  by (auto simp add: final_notin_def dest: exec.Call)

lemma notStuck_CallDefinedD: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}\<rbrakk> 
   \<Longrightarrow> \<Gamma> p \<noteq> None"
  by (cases "\<Gamma> p") 
     (auto simp add: final_notin_def dest:  exec.CallUndefined)

lemma notStuck_DynComD: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>DynCom c,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}\<rbrakk> 
   \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>(c s),Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}"
  by (auto simp add: final_notin_def dest: exec.DynCom)

lemma notStuck_CatchD1: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>Catch c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}"
  by (auto simp add: final_notin_def dest: exec.CatchMatch exec.CatchMiss )

lemma notStuck_CatchD2: 
  "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p\<langle>Catch c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}; \<Gamma>\<turnstile>\<^sub>p\<langle>c1,Normal s\<rangle> \<Rightarrow>Abrupt s'\<rbrakk> 
   \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<langle>c2,Normal s'\<rangle> \<Rightarrow>\<notin>{Stuck}"
  by (auto simp add: final_notin_def dest: exec.CatchMatch)


(* ************************************************************************* *)
subsection "Miscellaneous"
(* ************************************************************************* *)
lemma no_guards_bdy:"\<Gamma>1=\<Gamma>\<^sub>\<not>\<^sub>a \<Longrightarrow> 
                     \<forall>p \<in> dom \<Gamma>. noguards (the (\<Gamma> p)) 
                     \<Longrightarrow> \<forall>p \<in> dom \<Gamma>1. Language.noguards (the (\<Gamma>1 p))"
proof
  fix p
  assume a1:"\<Gamma>1 = \<Gamma>\<^sub>\<not>\<^sub>a"
  assume a2:"\<forall>p\<in>dom \<Gamma>. LanguageCon.noguards (the (\<Gamma> p))"
  assume a3:"p \<in> dom \<Gamma>1" 
  with a1 a2 obtain t where t:"\<Gamma> p = Some t"
     by (meson domD in_gamma_in_noawait_gamma)
  with a3 obtain s where s:"\<Gamma>1 p = Some s" by blast
  with t s a1 have noaw_t:"noawaits t" by (meson no_await_some_no_await)
  with a1 a3 s t lam1_seq have "s=sequential t" by fastforce
  moreover have "LanguageCon.noguards t" 
   using a2 t by force
  ultimately have "Language.noguards s" 
   using noaw_t noawaits_noguards_seq by blast
  then show "Language.noguards (the (\<Gamma>1 p))"by (simp add: s)
qed

lemma execn_noguards_no_Fault:
 assumes execn: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"
 assumes noguards_c: "noguards c"
 assumes noguards_\<Gamma>: "\<forall>p \<in> dom \<Gamma>. noguards (the (\<Gamma> p))"
 assumes s_no_Fault: "\<not> isFault s"
 shows "\<not> isFault t"
  using execn noguards_c s_no_Fault
  proof (induct) 
    case (Call p bdy n s t) with noguards_\<Gamma> show ?case
      apply -
      apply (drule bspec [where x=p])
      apply auto
      done
  next
    case (AwaitTrue s b \<Gamma>1 c n t) 
      with Semantic.execn_noguards_no_Fault no_guards_bdy 
      have s1:"\<forall>p \<in> dom \<Gamma>1. Language.noguards (the (\<Gamma>1 p))" using  noguards_\<Gamma>
      proof -
        have "\<forall>a. a \<notin> dom \<Gamma>1 \<or> Language.noguards (the (\<Gamma>1 a))"
          by (metis (no_types) AwaitTrue.hyps(2) no_guards_bdy noguards_\<Gamma>)
        then show ?thesis
          by metis
      qed             
      have "Language.noguards c"
        using AwaitTrue.prems(1) LanguageCon.noguards.simps(12) by blast
      hence "\<not> Semantic.isFault t"
        by (meson AwaitTrue.hyps(3) Semantic.isFault_simps(1) s1 execn_noguards_no_Fault)        
      thus ?case
        using SemanticCon.not_isFault_iff by force     
  qed (auto)

lemma exec_noguards_no_Fault:
 assumes exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t"
 assumes noguards_c: "noguards c"
 assumes noguards_\<Gamma>: "\<forall>p \<in> dom \<Gamma>. noguards (the (\<Gamma> p))"
 assumes s_no_Fault: "\<not> isFault s"
 shows "\<not> isFault t"
  using exec noguards_c s_no_Fault
  proof (induct) 
    case (Call p bdy s t) with noguards_\<Gamma> show ?case
      apply -
      apply (drule bspec [where x=p])
      apply auto
      done
  next
   case (AwaitTrue) thus ?case  
     by (meson Semantic.exec_to_execn SemanticCon.execn_noguards_no_Fault execn.AwaitTrue noguards_\<Gamma>)
  qed auto


lemma no_throws_bdy:"\<Gamma>1=\<Gamma>\<^sub>\<not>\<^sub>a \<Longrightarrow> \<forall>p \<in> dom \<Gamma>. nothrows (the (\<Gamma> p)) 
                     \<Longrightarrow> \<forall>p \<in> dom \<Gamma>1. Language.nothrows (the (\<Gamma>1 p))"
proof
  fix p
  assume a1:"\<Gamma>1 = \<Gamma>\<^sub>\<not>\<^sub>a"
  assume a2:"\<forall>p\<in>dom \<Gamma>. LanguageCon.nothrows (the (\<Gamma> p))"
  assume a3:"p \<in> dom \<Gamma>1" 
  with a1 a2 obtain t where t:"\<Gamma> p = Some t"
     by (meson domD in_gamma_in_noawait_gamma)
  with a3 obtain s where s:"\<Gamma>1 p = Some s" by blast
  with t s a1 have noaw_t:"noawaits t" by (meson no_await_some_no_await)
  with a1 a3 s t lam1_seq have "s=sequential t" by fastforce
  moreover have "LanguageCon.nothrows t" 
   using a2 t by force
  ultimately have "Language.nothrows s" 
   using noaw_t noawaits_nothrows_seq by blast
  then show "Language.nothrows (the (\<Gamma>1 p))"by (simp add: s)
qed

lemma execn_nothrows_no_Abrupt:
 assumes execn: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> =n\<Rightarrow> t"
 assumes nothrows_c: "nothrows c"
 assumes nothrows_\<Gamma>: "\<forall>p \<in> dom \<Gamma>. nothrows (the (\<Gamma> p))"
 assumes s_no_Abrupt: "\<not>(isAbr s)"
 shows "\<not>(isAbr t)"
  using execn nothrows_c s_no_Abrupt
  proof (induct) 
    case (Call p bdy n s t) with nothrows_\<Gamma> show ?case
      apply -
      apply (drule bspec [where x=p])
      apply auto
      done
  next    
 case (AwaitTrue s b \<Gamma>1 c n t) 
      with Semantic.execn_noguards_no_Fault no_throws_bdy 
      have s:"\<forall>p \<in> dom \<Gamma>1. Language.nothrows (the (\<Gamma>1 p))" using  nothrows_\<Gamma>
      proof -
        have "\<forall>a. a \<notin> dom \<Gamma>1 \<or> Language.nothrows (the (\<Gamma>1 a))"
          by (simp add: AwaitTrue.hyps(2) no_throws_bdy nothrows_\<Gamma>)
        then show ?thesis
          by metis
      qed         
      have "Language.nothrows c"
        using AwaitTrue.prems(1) LanguageCon.nothrows.simps(12) by blast
      hence "\<not> Semantic.isAbr t" 
       by (meson AwaitTrue.hyps(3) Semantic.execn_to_exec Semantic.isAbr_simps(1) s exec_nothrows_no_Abrupt)
      thus ?case using Semantic.isAbr_def SemanticCon.isAbrE by fastforce          
  qed (auto)

lemma exec_nothrows_no_Abrupt:
 assumes exec: "\<Gamma>\<turnstile>\<^sub>p\<langle>c,s\<rangle> \<Rightarrow> t"
 assumes nothrows_c: "nothrows c"
 assumes nothrows_\<Gamma>: "\<forall>p \<in> dom \<Gamma>. nothrows (the (\<Gamma> p))"
 assumes s_no_Abrupt: "\<not>(isAbr s)"
 shows "\<not>(isAbr t)"
  using exec nothrows_c s_no_Abrupt
  proof (induct) 
    case (Call p bdy s t) with nothrows_\<Gamma> show ?case
      apply -
      apply (drule bspec [where x=p])
      apply auto
      done
 next
   case (AwaitTrue) thus ?case  
     by (meson Semantic.exec_to_execn execn_nothrows_no_Abrupt execn.AwaitTrue nothrows_\<Gamma>)
  qed (auto)

end

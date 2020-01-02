(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      SyntaxTest.thy
    Author:     Norbert Schirmer, TU Muenchen

Copyright (C) 2006-2008 Norbert Schirmer 
Some rights reserved, TU Muenchen

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
(*<*)

theory SyntaxTest imports HeapList VcgCon begin


record Example1 =
  A :: "nat list"
  B :: "nat"

lemma "\<lbrace> (length \<ordmasculine>A = length \<ordfeminine>A) \<and> (\<ordmasculine>A ! i = \<ordfeminine>A ! i) \<rbrace> = 
         {x. (length (A (fst x)) = length (A (snd x))) \<and> 
             ((A (fst x))!i = (A (snd x))!i) }"
by auto

record "globals" =
 alloc_' :: "ref list"
 free_':: nat
 GA_' :: "ref list list"
 next_' :: "ref \<Rightarrow> ref"
 cont_' :: "ref \<Rightarrow> nat"

record localsd = 
  n1_' :: "nat"
  n2_' :: "ref \<Rightarrow> nat"

record ('g,'a) vars = "'g state" +
  A_' :: "nat list"
  AA_' :: "nat list list"
  I_' :: nat
  M_' :: nat
  N_' :: nat
  R_' :: int
  R1_' :: "'a list"
  S_' :: int
  B_' :: bool
  Abr_':: string
  p_' :: ref
  q_' :: ref
  d_' :: nat

record ('g,'a) vars1 = "'g state" +
  A_' :: "nat list"
  AA_' :: "nat list list"
  I_' :: nat
  M_' :: nat
  N_' :: nat
  R_' :: int
  R1_' :: "'a list"
  S_' :: int
  B_' :: bool
  Abr_':: string
  p_' :: ref
  q_' :: ref
  d_' :: nat

lemma "{..<3::nat} = {} \<Longrightarrow> False"
by (simp add: Iio_eq_empty_iff_nat)


lemma Example1:
 "\<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> (COBEGIN
      SCHEME [0 \<le> i < n]
     (SKIP,
     \<lbrace>\<acute>M = 0\<rbrace>,
     \<lbrace>(\<ordmasculine>M = \<ordfeminine>M)\<rbrace>\<^sub>r ,
     {(x,y). (\<exists>x1 y1. x=Normal x1 \<and> y=Normal y1 \<and> (M_' x1=  M_' y1))},
     \<lbrace> True \<rbrace>,
      \<lbrace> True \<rbrace>)
    COEND)
 SAT [\<lbrace>\<acute>M = 0\<rbrace>, {(x,y). (\<exists>x1 y1. x=Normal x1 \<and> y=Normal y1 \<and> (M_' x1=  M_' y1))},
     {(x,y). (\<exists>x1 y1. x=Normal x1 \<and> y=Normal y1 \<and> (M_' x1=  M_' y1))}, \<lbrace> True \<rbrace>, \<lbrace> True \<rbrace>]"
apply (rule Parallel)
apply (auto simp add:Pre_def Rely_def Com_def Guar_def Post_def Abr_def)
apply (auto intro!: Conseq)
apply(rule_tac x="\<lbrace>\<acute>M = 0\<rbrace>" in exI)
apply simp
apply(rule_tac x="{(x,y). (\<exists>x1 y1. x=Normal x1 \<and> y=Normal y1 \<and> (M_' x1=  M_' y1))}" in exI)
apply simp
apply(rule_tac x="{(x,y). (\<exists>x1 y1. x=Normal x1 \<and> y=Normal y1 \<and> (M_' x1=  M_' y1))}" in exI)
apply simp
apply(rule_tac x="\<lbrace>\<acute>M = 0\<rbrace>" in exI)
apply (subgoal_tac "lrghoare \<Gamma> {} {} SKIP \<lbrace>\<acute>M = 0\<rbrace>
                 {(x,y). (\<exists>x1 y1. x=Normal x1 \<and> y=Normal y1 \<and> (M_' x1=  M_' y1))}
                 {(x,y). (\<exists>x1 y1. x=Normal x1 \<and> y=Normal y1 \<and> (M_' x1=  M_' y1))} \<lbrace>\<acute>M = 0\<rbrace> \<lbrace>\<acute>M = 0\<rbrace>")
prefer 2
by (auto simp add: Norm_def Sta_def intro!:Skip)

thm Conseq LocalRG_HoareDef.Conseq
lemma Example2:
 "\<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> (COBEGIN
      SCHEME [0 \<le> i < n]
     (SKIP,
     \<lbrace>\<acute>M = 0\<rbrace>,
     {(x,y). (\<exists>x1 y1. x=Normal x1 \<and> y=Normal y1 \<and> x=y)},
     {(x,y). (\<exists>x1 y1. x=Normal x1 \<and> y=Normal y1 \<and> x=y)},
     \<lbrace> True \<rbrace>,
      \<lbrace> True \<rbrace>)
    COEND)
 SAT [\<lbrace>\<acute>M = 0\<rbrace>, {(x,y). (\<exists>x1 y1. x=Normal x1 \<and> y=Normal y1 \<and> x=y)},
     {(x,y). (\<exists>x1 y1. x=Normal x1 \<and> y=Normal y1 \<and> x=y)}, \<lbrace> True \<rbrace>, \<lbrace> True \<rbrace>]"
apply (rule Parallel)
apply (auto simp add:Pre_def Rely_def Com_def Guar_def Post_def Abr_def)
apply (auto intro!: Conseq)
apply(rule_tac x="\<lbrace>\<acute>M = 0\<rbrace>" in exI)
apply simp
apply(rule_tac x="{(x,y). (\<exists>x1 y1. x=Normal x1 \<and> y=Normal y1 \<and> x=y)}" in exI)
apply simp
apply(rule_tac x="{(x,y). (\<exists>x1 y1. x=Normal x1 \<and> y=Normal y1 \<and> x=y)}" in exI)
apply simp
apply(rule_tac x="\<lbrace>\<acute>M = 0\<rbrace>" in exI)
apply (subgoal_tac "lrghoare \<Gamma> {} {} SKIP \<lbrace>\<acute>M = 0\<rbrace>
                {(x, y). (\<exists>x1. x = Normal x1) \<and> (\<exists>y1. y = Normal y1) \<and> x = y}
                {(x, y). (\<exists>x1. x = Normal x1) \<and> (\<exists>y1. y = Normal y1) \<and> x = y} \<lbrace>\<acute>M = 0\<rbrace> \<lbrace>\<acute>M = 0\<rbrace>")
prefer 2
apply (rule Skip)
apply (simp add: Sta_def)
apply (simp add: Norm_def)
apply (simp add: Norm_def)
by auto


lemma Example3:
 "\<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> (COBEGIN
      SCHEME [0 \<le> i < n]
     (SKIP,
     \<lbrace> True \<rbrace>,
     \<lbrace>True \<rbrace>,
     \<lbrace> True \<rbrace>,
     \<lbrace> True \<rbrace>,
     \<lbrace> True \<rbrace>)
    COEND)
 SAT [\<lbrace> True \<rbrace>, \<lbrace> True \<rbrace>, \<lbrace> True \<rbrace>, \<lbrace> True \<rbrace>, \<lbrace> True \<rbrace>]"
apply (auto simp add: Parallel)
apply (rule Parallel)
apply (auto simp add:Pre_def Rely_def Com_def Guar_def Post_def Abr_def)
apply (rule Skip)
apply (auto intro!: Skip simp:Sta_def Norm_def)[1]
sorry



(*lemma Example1:
 "\<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> (COBEGIN
      SCHEME [0 \<le> i < n]
     (\<acute>A :== \<acute>A [i := 0],
     \<lbrace> n < length \<acute>A \<rbrace>,
     \<lbrace> length \<ordmasculine>A = length \<ordfeminine>A \<and> \<ordmasculine>A ! i = \<ordfeminine>A ! i \<rbrace>,
     \<lbrace> length \<ordmasculine>A = length \<ordfeminine>A \<and> (\<forall>j<n. i \<noteq> j \<longrightarrow> \<ordmasculine>A ! j = \<ordfeminine>A ! j) \<rbrace>,
     \<lbrace> \<acute>A ! i = 0 \<rbrace>)
    COEND)
 sat [\<lbrace> n < length \<acute>A \<rbrace>, \<lbrace> \<ordmasculine>A = \<ordfeminine>A \<rbrace>, \<lbrace> True \<rbrace>, \<lbrace> \<forall>i < n. \<acute>A ! i = 0 \<rbrace>, \<lbrace> \<forall>i < n. \<acute>A ! i = 0 \<rbrace>]"
*)




hoarestate h = PA :: nat

hoarestate h1 = h + KA::nat
                    v::ref
                    q_' :: ref
                    free_':: nat
                    d_'::nat
 


procedures (imports h1)  Foo (q,d|d) = "\<acute>q :== \<acute>q;;\<acute>free:==0;;\<acute>d:==0"

context Foo_impl
begin
thm Foo_impl
thm Foo_body_def
end
context h1
begin
term  "\<acute>KA :== 3 -1 ;; \<acute>PA:==1"
end

term "\<acute>n1 :==\<^sub>g 3 - 1"
term "\<acute>I :==\<^sub>g \<acute>free"
term "\<acute>R :==\<^sub>g 3 - 1"
term "\<acute>I :==\<^sub>g \<acute>A!i"
term " \<acute>A!i :== j"
term " \<acute>AA :== \<acute>AA!![i,j]"
term " \<acute>AA!![i,j] :== \<acute>AA"
term "\<acute>A!i :==\<^sub>g j"
term "\<acute>p :==\<^sub>g \<acute>GA!i!j"
term "\<acute>p :==\<^sub>g \<acute>GA!i!j"
term "\<acute>GA!i!j :==\<^sub>g \<acute>p"
term "\<acute>p :==\<^sub>g \<acute>p \<rightarrow> \<acute>next"
term "\<acute>p \<rightarrow> \<acute>next :==\<^sub>g \<acute>p"
term "\<acute>p \<rightarrow> \<acute>next \<rightarrow> \<acute>next :==\<^sub>g \<acute>p"
term "\<acute>p :== NEW sz [\<acute>next :== Null,\<acute>cont :== 0]"
term "\<acute>p\<rightarrow>\<acute>next :==\<^sub>g NEW sz [\<acute>next :== Null,\<acute>cont :== 0]"
term "\<acute>p :== NNEW sz [\<acute>next :== Null,\<acute>cont :== 0]"
term "\<acute>p\<rightarrow>\<acute>next :==\<^sub>g NNEW sz [\<acute>next :== Null,\<acute>cont :== 0]"
term "\<acute>B :==\<^sub>g \<acute>N + 1 < 0 \<and> \<acute>M + \<acute>N < n"
term "\<acute>B :==\<^sub>g \<acute>N + 1 < 0 \<or>  \<acute>M + \<acute>N < n"
term "\<acute>I :==\<^sub>g \<acute>N mod n"
term "\<acute>I :==\<^sub>g \<acute>N div n"
term "\<acute>R :==\<^sub>g \<acute>R div n"
term "\<acute>R :==\<^sub>g \<acute>R mod n"
term "\<acute>R :==\<^sub>g \<acute>R * n"
term "\<acute>I :==\<^sub>g \<acute>I - \<acute>N"
term "\<acute>R :==\<^sub>g \<acute>R - \<acute>S"
term "\<acute>R :==\<^sub>g int \<acute>I"
term "\<acute>I :==\<^sub>g nat \<acute>R"
term "\<acute>R :==\<^sub>g -\<acute>R"
term "IF\<^sub>g \<acute>A!i < \<acute>N THEN c1 ELSE c2 FI"
term "AWAIT\<^sub>g \<acute>A!i < \<acute>N (IF True THEN SKIP ELSE SKIP FI)"
term "WHILE\<^sub>g \<acute>A!i < \<acute>N DO c OD"
term "WHILE\<^sub>g \<acute>A!i < \<acute>N INV \<lbrace>foo\<rbrace> DO c OD"
term "WHILE\<^sub>g \<acute>A!i < \<acute>N INV \<lbrace>foo\<rbrace> VAR bar x DO c OD"
term "WHILE\<^sub>g \<acute>A!i < \<acute>N INV \<lbrace>foo\<rbrace> VAR bar x DO c OD;;cd"
term "c;;WHILE\<^sub>g \<acute>A!i < \<acute>N INV \<lbrace>foo\<rbrace> VAR MEASURE \<acute>N + \<acute>M DO c;;c OD;;c"
context Foo_impl
begin
term "\<acute>q :== CALL Foo(\<acute>p,\<acute>M)" 
term "\<acute>q :== CALL\<^sub>g Foo(\<acute>p,\<acute>M + 1)" 
term "\<acute>q :== CALL Foo(\<acute>p\<rightarrow>\<acute>next,\<acute>M)" 
term "\<acute>q \<rightarrow> \<acute>next :== CALL Foo(\<acute>p,\<acute>M)" 
term "COBEGIN (\<acute>q :== CALL Foo(\<acute>p\<rightarrow>\<acute>next,\<acute>M)) \<parallel> (\<acute>q :== CALL Foo(\<acute>p\<rightarrow>\<acute>next,\<acute>M)) COEND"
end

end

(*>*) 
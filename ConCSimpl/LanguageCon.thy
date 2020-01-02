(*
    Author:      David Sanan
    Maintainer:  David Sanan, sanan at ntu edu sg
    License:     LGPL
*)

(*  Title:      LanguageCon.thy
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

section {* The Simpl Syntax *}

theory LanguageCon imports "HOL-Library.Old_Recdef" "EmbSimpl.Language" begin

subsection {* The Core Language *}

text {* We use a shallow embedding of boolean expressions as well as assertions
as sets of states. 
*}

type_synonym 's bexp = "'s set"
type_synonym 's assn = "'s set"

datatype (dead 's, 'p, 'f, dead 'e) com =
    Skip
  | Basic "'s \<Rightarrow> 's" "'e option"
  | Spec "('s \<times> 's) set"  "'e option"
  | Seq "('s ,'p, 'f,'e) com" "('s,'p, 'f,'e) com"    
  | Cond "'s bexp" "('s,'p,'f,'e) com"  "('s,'p,'f,'e) com"
  | While "'s bexp" "('s,'p,'f,'e) com"
  | Call "'p" 
  | DynCom "'s \<Rightarrow> ('s,'p,'f,'e) com" 
  | Guard "'f" "'s bexp" "('s,'p,'f,'e) com" 
  | Throw
  | Catch "('s,'p,'f,'e) com" "('s,'p,'f,'e) com"
  | Await "'s bexp" "('s,'p,'f) Language.com" "'e option"


primrec sequential:: "('s, 'p, 'f, 'e) com \<Rightarrow> ('s,'p,'f) Language.com"
where
"sequential Skip = Language.Skip" |
"sequential (Basic f e) = Language.Basic f" |
"sequential (Spec r e) = Language.Spec r" |
"sequential (Seq c\<^sub>1 c\<^sub>2)  = Language.Seq (sequential c\<^sub>1) (sequential c\<^sub>2)" |
"sequential (Cond b c\<^sub>1 c\<^sub>2) = Language.Cond b (sequential c\<^sub>1) (sequential c\<^sub>2)" |
"sequential (While b c) = Language.While b (sequential c)" |
"sequential (Call p) = Language.Call p" |
"sequential (DynCom c) = Language.DynCom (\<lambda>s. (sequential (c s)))" |
"sequential (Guard f g c) = Language.Guard f g (sequential c)" |
"sequential Throw = Language.Throw" |
"sequential (Catch c\<^sub>1 c\<^sub>2) = Language.Catch (sequential c\<^sub>1) (sequential c\<^sub>2)" |
"sequential (Await b ca e) = Language.Skip"

primrec parallel:: "('s,'p,'f)  Language.com \<Rightarrow> ('s,'p,'f,'e) com"
where
"parallel Language.Skip = Skip" |
"parallel (Language.Basic f) = Basic f None" |
"parallel (Language.Spec r) = Spec r None" |
"parallel (Language.Seq c\<^sub>1 c\<^sub>2)  = Seq (parallel c\<^sub>1) (parallel c\<^sub>2)" |
"parallel (Language.Cond b c\<^sub>1 c\<^sub>2) = Cond b (parallel c\<^sub>1) (parallel c\<^sub>2)" |
"parallel (Language.While b c) = While b (parallel c)" |
"parallel (Language.Call p) = Call p" |
"parallel (Language.DynCom c) = DynCom (\<lambda>s. (parallel (c s)))" |
"parallel (Language.Guard f g c) = Guard f g (parallel c)" |
"parallel Language.Throw = Throw" |
"parallel (Language.Catch c\<^sub>1 c\<^sub>2) = Catch (parallel c\<^sub>1) (parallel c\<^sub>2)"


primrec noawaits:: "('s, 'p, 'f, 'e) com \<Rightarrow> bool"
where
"noawaits Skip = True" |
"noawaits (Basic f e) = True" |
"noawaits (Spec r e) = True" |
"noawaits (Seq c\<^sub>1 c\<^sub>2)  = (noawaits c\<^sub>1 \<and> noawaits c\<^sub>2)" |
"noawaits (Cond b c\<^sub>1 c\<^sub>2) = (noawaits c\<^sub>1 \<and> noawaits c\<^sub>2)" |
"noawaits (While b c) = (noawaits c)" |
"noawaits (Call p) = True" |
"noawaits (DynCom c) = (\<forall>s. noawaits (c s))" |
"noawaits (Guard f g c) = noawaits c" |
"noawaits Throw = True" |
"noawaits (Catch c\<^sub>1 c\<^sub>2) = (noawaits c\<^sub>1 \<and> noawaits c\<^sub>2)" |
"noawaits (Await b cn e) = False"

subsection {* Derived Language Constructs *}

definition
  raise:: "('s \<Rightarrow> 's) \<Rightarrow> 'e option \<Rightarrow> ('s, 'p, 'f, 'e) com" where
  "raise f e = Seq (Basic f e) Throw"

definition
  condCatch:: "('s, 'p, 'f, 'e) com \<Rightarrow> 's bexp \<Rightarrow> ('s, 'p, 'f, 'e) com \<Rightarrow> ('s, 'p, 'f, 'e) com" where
  "condCatch c\<^sub>1 b c\<^sub>2 = Catch c\<^sub>1 (Cond b c\<^sub>2 Throw)"

definition
  bind:: "('s \<Rightarrow> 'v) \<Rightarrow> ('v \<Rightarrow> ('s, 'p, 'f, 'e) com) \<Rightarrow> ('s, 'p, 'f, 'e) com" where
  "bind e c = DynCom (\<lambda>s. c (e s))"

definition
  bseq:: "('s, 'p, 'f, 'e) com \<Rightarrow> ('s, 'p, 'f, 'e) com \<Rightarrow> ('s, 'p, 'f, 'e) com" where
  "bseq = Seq"
 
definition
  block:: "['s\<Rightarrow>'s,'e option, ('s, 'p, 'f, 'e) com, 's\<Rightarrow>'s\<Rightarrow>'s, 'e option, 's\<Rightarrow>'s\<Rightarrow>('s, 'p, 'f, 'e) com]\<Rightarrow>('s, 'p, 'f, 'e) com"
where
  "block init ei bdy return er c =
    DynCom (\<lambda>s. (Seq (Catch (Seq (Basic init ei) bdy) (Seq (Basic (return s) er) Throw)) 
                            (DynCom (\<lambda>t. Seq (Basic (return s) er) (c s t))))
                        )" 

definition
  call:: "('s\<Rightarrow>'s) \<Rightarrow> 'e option \<Rightarrow> 'p \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 's)\<Rightarrow> 'e option \<Rightarrow> ('s\<Rightarrow>'s\<Rightarrow>('s, 'p, 'f, 'e) com)\<Rightarrow>('s, 'p, 'f, 'e) com" where
  "call init ei p return er c = block init ei (Call p) return er c"

definition
  dynCall:: "('s \<Rightarrow> 's) \<Rightarrow> 'e option \<Rightarrow> ('s \<Rightarrow> 'p) \<Rightarrow> 
             ('s \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 'e option \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> ('s, 'p, 'f, 'e) com) \<Rightarrow> ('s, 'p, 'f, 'e) com" where
  "dynCall init ei p return er c = DynCom (\<lambda>s. call init ei (p s) return er c)"

definition
  fcall:: "('s\<Rightarrow>'s) \<Rightarrow> 'e option \<Rightarrow> 'p \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 's)\<Rightarrow> 'e option \<Rightarrow> ('s \<Rightarrow> 'v) \<Rightarrow> ('v\<Rightarrow>('s, 'p, 'f, 'e) com)
            \<Rightarrow>('s, 'p, 'f, 'e) com" where
  "fcall init ei p return er result c = call init ei p return er (\<lambda>s t. c (result t))"

definition
  lem:: "'x \<Rightarrow> ('s, 'p, 'f, 'e) com \<Rightarrow>('s, 'p, 'f, 'e) com" where
  "lem x c = c"

primrec switch:: "('s \<Rightarrow> 'v) \<Rightarrow> ('v set \<times> ('s, 'p, 'f, 'e) com) list \<Rightarrow> ('s, 'p, 'f, 'e) com" 
where
"switch v [] = Skip" |
"switch v (Vc#vs) = Cond {s. v s \<in> fst Vc} (snd Vc) (switch v vs)"

definition guaranteeStrip:: "'f \<Rightarrow> 's set \<Rightarrow> ('s, 'p, 'f, 'e) com \<Rightarrow> ('s, 'p, 'f, 'e) com"
  where "guaranteeStrip f g c = Guard f g c"

definition guaranteeStripPair:: "'f \<Rightarrow> 's set \<Rightarrow> ('f \<times> 's set)"
  where "guaranteeStripPair f g = (f,g)"

primrec guards:: "('f \<times> 's set ) list \<Rightarrow> ('s, 'p, 'f, 'e) com \<Rightarrow> ('s, 'p, 'f, 'e) com"
where
"guards [] c = c" |
"guards (g#gs) c = Guard (fst g) (snd g) (guards gs c)"

definition
  while::  "('f \<times> 's set) list \<Rightarrow> 's bexp \<Rightarrow> ('s, 'p, 'f, 'e) com \<Rightarrow> ('s, 'p, 'f, 'e) com"
where
  "while gs b c = guards gs (While b (Seq c (guards gs Skip)))"

definition
  whileAnno:: 
  "'s bexp \<Rightarrow> 's assn \<Rightarrow> ('s \<times> 's) assn \<Rightarrow> ('s, 'p, 'f, 'e) com \<Rightarrow> ('s, 'p, 'f, 'e) com" where
  "whileAnno b I V c = While b c"

definition
  whileAnnoG:: 
  "('f \<times> 's set) list \<Rightarrow> 's bexp \<Rightarrow> 's assn \<Rightarrow> ('s \<times> 's) assn \<Rightarrow> 
     ('s, 'p, 'f, 'e) com \<Rightarrow> ('s, 'p, 'f, 'e) com" where
  "whileAnnoG gs b I V c = while gs b c"
 
definition
  specAnno::  "('a \<Rightarrow> 's assn) \<Rightarrow> ('a \<Rightarrow> ('s, 'p, 'f, 'e) com) \<Rightarrow> 
                         ('a \<Rightarrow> 's assn) \<Rightarrow> ('a \<Rightarrow> 's assn) \<Rightarrow> ('s, 'p, 'f, 'e) com"
  where "specAnno P c Q A = (c undefined)"

definition
  whileAnnoFix:: 
  "'s bexp \<Rightarrow> ('a \<Rightarrow> 's assn) \<Rightarrow> ('a \<Rightarrow> ('s \<times> 's) assn) \<Rightarrow> ('a \<Rightarrow> ('s, 'p, 'f, 'e) com) \<Rightarrow> 
     ('s, 'p, 'f, 'e) com" where
  "whileAnnoFix b I V c = While b (c undefined)"

definition
  whileAnnoGFix:: 
  "('f \<times> 's set) list \<Rightarrow> 's bexp \<Rightarrow> ('a \<Rightarrow> 's assn) \<Rightarrow> ('a \<Rightarrow> ('s \<times> 's) assn) \<Rightarrow> 
     ('a \<Rightarrow> ('s, 'p, 'f, 'e) com) \<Rightarrow> ('s, 'p, 'f, 'e) com" where
  "whileAnnoGFix gs b I V c = while gs b (c undefined)"

definition if_rel::"('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<times> 's) set" 
  where "if_rel b f g h = {(s,t). if b s then t = f s else t = g s \<or> t = h s}"

lemma fst_guaranteeStripPair: "fst (guaranteeStripPair f g) = f"
  by (simp add: guaranteeStripPair_def)

lemma snd_guaranteeStripPair: "snd (guaranteeStripPair f g) = g"
  by (simp add: guaranteeStripPair_def)


subsection {* Operations on Simpl-Syntax *}


subsubsection {* Normalisation of Sequential Composition: @{text "sequence"}, @{text "flatten"} and @{text "normalize"} *}

primrec flatten:: "('s, 'p, 'f, 'e) com \<Rightarrow> ('s, 'p, 'f, 'e) com list" 
where
"flatten Skip = [Skip]" |
"flatten (Basic f e) = [Basic f e]" |
"flatten (Spec r e) = [Spec r e]" |
"flatten (Seq c\<^sub>1 c\<^sub>2)  = flatten c\<^sub>1 @ flatten c\<^sub>2" |
"flatten (Cond b c\<^sub>1 c\<^sub>2) = [Cond b c\<^sub>1 c\<^sub>2]" |
"flatten (While b c) = [While b c]" |
"flatten (Call p) = [Call p]" |
"flatten (DynCom c) = [DynCom c]" |
"flatten (Guard f g c) = [Guard f g c]" |
"flatten Throw = [Throw]" |
"flatten (Catch c\<^sub>1 c\<^sub>2) = [Catch c\<^sub>1 c\<^sub>2]" |
"flatten (Await b ca e) = [Await b ca e]"

primrec flattenc:: "('s, 'p, 'f, 'e) com \<Rightarrow> ('s, 'p, 'f, 'e) com list" 
where
"flattenc Skip = [Skip]" |
"flattenc (Basic f e) = [Basic f e]" |
"flattenc (Spec r e) = [Spec r e]" |
"flattenc (Seq c\<^sub>1 c\<^sub>2)  = [Seq c\<^sub>1 c\<^sub>2]" |
"flattenc (Cond b c\<^sub>1 c\<^sub>2) = [Cond b c\<^sub>1 c\<^sub>2]" |
"flattenc (While b c) = [While b c]" |
"flattenc (Call p) = [Call p]" |
"flattenc (DynCom c) = [DynCom c]" |
"flattenc (Guard f g c) = [Guard f g c]" |
"flattenc Throw = [Throw]" |
"flattenc (Catch c\<^sub>1 c\<^sub>2) = flattenc c\<^sub>1 @ flattenc c\<^sub>2" |
"flattenc (Await b ca e) = [Await b ca e]"

primrec sequence:: "(('s, 'p, 'f, 'e) com \<Rightarrow> ('s, 'p, 'f, 'e) com \<Rightarrow> ('s, 'p, 'f, 'e) com) \<Rightarrow> 
                      ('s, 'p, 'f, 'e) com list \<Rightarrow> ('s, 'p, 'f, 'e) com"
where
"sequence seq [] = Skip" |
"sequence seq (c#cs) = (case cs of [] \<Rightarrow> c
                        | _ \<Rightarrow> seq c (sequence seq cs))" 


primrec normalize:: "('s, 'p, 'f, 'e) com \<Rightarrow> ('s, 'p, 'f, 'e) com"
where
"normalize Skip = Skip" |
"normalize (Basic f e) = Basic f e" |
"normalize (Spec r e) = Spec r e" |
"normalize (Seq c\<^sub>1 c\<^sub>2)  = sequence Seq
                            ((flatten (normalize c\<^sub>1)) @ (flatten (normalize c\<^sub>2)))" |
"normalize (Cond b c\<^sub>1 c\<^sub>2) = Cond b (normalize c\<^sub>1) (normalize c\<^sub>2)" |
"normalize (While b c) = While b (normalize c)" |
"normalize (Call p) = Call p" |
"normalize (DynCom c) = DynCom (\<lambda>s. (normalize (c s)))" |
"normalize (Guard f g c) = Guard f g (normalize c)" |
"normalize Throw = Throw" |
"normalize (Catch c\<^sub>1 c\<^sub>2) = Catch (normalize c\<^sub>1) (normalize c\<^sub>2)" |
"normalize (Await b ca e) = Await b (Language.normalize ca) e"

primrec normalizec:: "('s, 'p, 'f, 'e) com \<Rightarrow> ('s, 'p, 'f, 'e) com"
where
"normalizec Skip = Skip" |
"normalizec (Basic f e) = Basic f e" |
"normalizec (Spec r e) = Spec r e" |
"normalizec (Seq c\<^sub>1 c\<^sub>2)  = Seq (normalizec c\<^sub>1) (normalizec c\<^sub>2)" |
"normalizec (Cond b c\<^sub>1 c\<^sub>2) = Cond b (normalizec c\<^sub>1) (normalizec c\<^sub>2)" |
"normalizec (While b c) = While b (normalizec c)" |
"normalizec (Call p) = Call p" |
"normalizec (DynCom c) = DynCom (\<lambda>s. (normalizec (c s)))" |
"normalizec (Guard f g c) = Guard f g (normalizec c)" |
"normalizec Throw = Throw" |
"normalizec (Catch c\<^sub>1 c\<^sub>2) = sequence Catch
                            ((flattenc (normalizec c\<^sub>1)) @ (flattenc (normalizec c\<^sub>2)))" |
"normalizec (Await b ca e) = Await b (Language.normalize ca) e"

lemma flatten_nonEmpty: "flatten c \<noteq> []"
  by (induct c) simp_all    

lemma flattenc_nonEmpty: "flattenc c \<noteq> []"
  by (induct c) simp_all

lemma flatten_single: "\<forall>c \<in> set (flatten c'). flatten c = [c]"
apply (induct c')
apply             simp
apply            simp
apply           simp
apply          (simp (no_asm_use) )
apply          blast
apply         (simp (no_asm_use) )
apply        (simp (no_asm_use) )
apply       simp
apply      (simp (no_asm_use))
apply     (simp (no_asm_use))
apply    simp
apply   (simp (no_asm_use))
apply    simp
done

lemma flattenc_single: "\<forall>c \<in> set (flattenc c'). flattenc c = [c]"
apply (induct c')
apply             simp
apply            simp
apply           simp
apply          (simp (no_asm_use) )
apply         (simp (no_asm_use) )
apply        (simp (no_asm_use) )
apply       simp
apply      (simp (no_asm_use))
apply     (simp (no_asm_use))
apply    simp
apply   (simp (no_asm_use))
apply    blast
apply    simp
done


lemma flatten_sequence_id: 
  "\<lbrakk>cs\<noteq>[];\<forall>c \<in> set cs. flatten c = [c]\<rbrakk> \<Longrightarrow> flatten (sequence Seq cs) = cs"
  apply (induct cs)
  apply  simp
  apply (case_tac cs)
  apply  simp
  apply auto
  done

lemma flattenc_sequence_id: 
  "\<lbrakk>cs\<noteq>[];\<forall>c \<in> set cs. flattenc c = [c]\<rbrakk> \<Longrightarrow> flattenc (sequence Catch cs) = cs"
  apply (induct cs)
  apply  simp
  apply (case_tac cs)
  apply  simp
  apply auto
  done

lemma flatten_app:
  "flatten (sequence Seq (flatten c1 @ flatten c2)) = flatten c1 @ flatten c2"
  apply (rule flatten_sequence_id)
  apply (simp add: flatten_nonEmpty)
  apply (simp)
  apply (insert flatten_single)
  apply blast
  done

lemma flattenc_app:
  "flattenc (sequence Catch (flattenc c1 @ flattenc c2)) = flattenc c1 @ flattenc c2"
  apply (rule flattenc_sequence_id)
  apply (simp add: flattenc_nonEmpty)
  apply (simp)
  apply (insert flattenc_single)
  apply blast
  done
  
lemma flatten_sequence_flatten: "flatten (sequence Seq (flatten c)) = flatten c"
  apply (induct c)
  apply (auto simp add: flatten_app)
  done


(* lemma "Seq (sequence Seq (flatten c1)) c2' = sequence Seq (flatten (Seq c1 c2'))"
proof (induct c1) print_cases
  case Skip 
  then have "sequence Seq (flatten Skip) = Skip" by auto
   have "sequence Seq (Skip#(flatten c2')) = sequence Seq (flatten (Seq Skip c2'))" by auto
   also have "sequence Seq (Skip#(flatten c2')) = Seq Skip (sequence Seq (flatten c2'))"
     using flatten_nonEmpty sequence.simps(2)[of Seq Skip "flatten c2'"]
     by (simp add: LanguageCon.flatten_nonEmpty list.case_eq_if)  
   finally show ?case
   have "LanguageCon.com.Seq Skip c2' = 
         LanguageCon.com.Seq (LanguageCon.sequence LanguageCon.com.Seq (LanguageCon.flatten LanguageCon.com.Skip)) c2'"
   by auto 
  finally show ?case
  then 
qed(auto)
*)

lemma flattenc_sequence_flattenc: "flattenc (sequence Catch (flattenc c)) = flattenc c"
  apply (induct c)
  apply (auto simp add: flattenc_app)
  done

lemma sequence_flatten_normalize: "sequence Seq (flatten (normalize c)) = normalize c"
apply (induct c)
apply (auto simp add:  flatten_app)
done

lemma sequence_flattenc_normalize: "sequence Catch (flattenc (normalizec c)) = normalizec c"
apply (induct c)
apply (auto simp add:  flattenc_app)
done


lemma flatten_normalize: "\<And>x xs. flatten (normalize c) = x#xs 
       \<Longrightarrow> (case xs of [] \<Rightarrow> normalize c = x 
              | (x'#xs') \<Rightarrow> normalize c= Seq x (sequence Seq xs))"
proof (induct c)
  case (Seq c1 c2)
  have "flatten (normalize (Seq c1 c2)) = x # xs" by fact
  hence "flatten (sequence Seq (flatten (normalize c1) @ flatten (normalize c2))) = 
          x#xs"
    by simp
  hence x_xs: "flatten (normalize c1) @ flatten (normalize c2) = x # xs" 
    by (simp add: flatten_app)
  show ?case
  proof (cases "flatten (normalize c1)")
    case Nil
    with flatten_nonEmpty show ?thesis by auto
  next
    case (Cons x1 xs1)
    note Cons_x1_xs1 = this
    with x_xs obtain 
      x_x1: "x=x1" and xs_rest: "xs=xs1@flatten (normalize c2)"
      by auto
    show ?thesis
    proof (cases xs1)
      case Nil
      from Seq.hyps (1) [OF Cons_x1_xs1] Nil
      have "normalize c1 = x1"
        by simp
      with Cons_x1_xs1 Nil x_x1 xs_rest show ?thesis
        apply (cases "flatten (normalize c2)")
        apply (fastforce simp add: flatten_nonEmpty)
        apply simp
        done
    next
      case Cons
      from Seq.hyps (1) [OF Cons_x1_xs1] Cons
      have "normalize c1 = Seq x1 (sequence Seq xs1)"
        by simp
      with Cons_x1_xs1 Nil x_x1 xs_rest show ?thesis
        apply (cases "flatten (normalize c2)")
        apply (fastforce simp add: flatten_nonEmpty)
        apply (simp split: list.splits)
        done
    qed
  qed
qed (auto)

lemma flattenc_normalizec: "\<And>x xs. flattenc (normalizec c) = x#xs 
       \<Longrightarrow> (case xs of [] \<Rightarrow> normalizec c = x 
              | (x'#xs') \<Rightarrow> normalizec c= Catch x (sequence Catch xs))"
proof (induct c)
  case (Catch c1 c2)
  have "flattenc (normalizec (Catch c1 c2)) = x # xs" by fact
  hence "flattenc (sequence Catch (flattenc (normalizec c1) @ flattenc (normalizec c2))) = 
          x#xs"
    by simp
  hence x_xs: "flattenc (normalizec c1) @ flattenc (normalizec c2) = x # xs" 
    by (simp add: flattenc_app)
  show ?case
  proof (cases "flattenc (normalizec c1)")
    case Nil
    with flattenc_nonEmpty show ?thesis by auto
  next
    case (Cons x1 xs1)
    note Cons_x1_xs1 = this
    with x_xs obtain 
      x_x1: "x=x1" and xs_rest: "xs=xs1@flattenc (normalizec c2)"
      by auto
    show ?thesis
    proof (cases xs1)
      case Nil
      from Catch.hyps (1) [OF Cons_x1_xs1] Nil
      have "normalizec c1 = x1"
        by simp
      with Cons_x1_xs1 Nil x_x1 xs_rest show ?thesis
        apply (cases "flattenc (normalizec c2)")
        apply (fastforce simp add: flattenc_nonEmpty)
        apply simp
        done
    next
      case Cons
      from Catch.hyps (1) [OF Cons_x1_xs1] Cons
      have "normalizec c1 = Catch x1 (sequence Catch xs1)"
        by simp
      with Cons_x1_xs1 Nil x_x1 xs_rest show ?thesis
        apply (cases "flattenc (normalizec c2)")
        apply (fastforce simp add: flattenc_nonEmpty)
        apply (simp split: list.splits)
        done
    qed
  qed
qed (auto)

lemma flatten_raise [simp]: "flatten (raise f e) = [Basic f e, Throw]"
  by (simp add: raise_def)

lemma flatten_condCatch [simp]: "flatten (condCatch c1 b c2) = [condCatch c1 b c2]"
  by (simp add: condCatch_def)

lemma flatten_bind [simp]: "flatten (bind e c) = [bind e c]"
  by (simp add: bind_def)

lemma flatten_bseq [simp]: "flatten (bseq c1 c2) = flatten c1 @ flatten c2"
  by (simp add: bseq_def)

lemma flatten_block [simp]:
  "flatten (block init ei bdy return er result) = [block init ei bdy return er result]"
  by (simp add: block_def)

lemma flatten_call [simp]: "flatten (call init ei p return er result) = [call init ei p return er result]"
  by (simp add: call_def)

lemma flatten_dynCall [simp]: "flatten (dynCall init ei p return er result) = [dynCall init ei p return er result]"
  by (simp add: dynCall_def)

lemma flatten_fcall [simp]: "flatten (fcall init ei p return er result c) = [fcall init ei p return er result c]"
  by (simp add: fcall_def)

lemma flatten_switch [simp]: "flatten (switch v Vcs) = [switch v Vcs]"
  by (cases Vcs) auto

lemma flatten_guaranteeStrip [simp]: 
  "flatten (guaranteeStrip f g c) = [guaranteeStrip f g c]"
  by (simp add: guaranteeStrip_def)

lemma flatten_while [simp]: "flatten (while gs b c) = [while gs b c]"
  apply (simp add: while_def)
  apply (induct gs)
  apply  auto
  done

lemma flatten_whileAnno [simp]: 
  "flatten (whileAnno b I V c) = [whileAnno b I V c]"
  by (simp add: whileAnno_def)

lemma flatten_whileAnnoG [simp]: 
  "flatten (whileAnnoG gs b I V c) = [whileAnnoG gs b I V c]"
  by (simp add: whileAnnoG_def)

lemma flatten_specAnno [simp]:
  "flatten (specAnno P c Q A) = flatten (c undefined)"
  by (simp add: specAnno_def)

lemmas flatten_simps = flatten.simps flatten_raise flatten_condCatch flatten_bind
  flatten_block flatten_call flatten_dynCall flatten_fcall flatten_switch
  flatten_guaranteeStrip
  flatten_while flatten_whileAnno flatten_whileAnnoG flatten_specAnno

lemma normalize_raise [simp]:
 "normalize (raise f e) = raise f e"
  by (simp add: raise_def)

lemma normalize_condCatch [simp]:
 "normalize (condCatch c1 b c2) = condCatch (normalize c1) b (normalize c2)"
  by (simp add: condCatch_def)

lemma normalize_bind [simp]:
 "normalize (bind e c) = bind e (\<lambda>v. normalize (c v))"
  by (simp add: bind_def)

lemma normalize_bseq [simp]:
 "normalize (bseq c1 c2) = sequence bseq
                            ((flatten (normalize c1)) @ (flatten (normalize c2)))"
  by (simp add: bseq_def)

lemma normalize_block [simp]: "normalize (block init ei bdy return er c) = 
                         block init ei (normalize bdy) return er (\<lambda>s t. normalize (c s t))"
  apply (simp add: block_def)
  apply (rule ext)
  apply (simp)
  apply (cases "flatten (normalize bdy)")
  apply  (simp add: flatten_nonEmpty)
  apply (rule conjI)
  apply  simp
  apply  (drule flatten_normalize)
  apply  (case_tac list)
  apply   simp
  apply  simp
  apply (rule ext)
  apply (case_tac "flatten (normalize (c s sa))")
  apply  (simp add: flatten_nonEmpty)
  apply  simp
  apply (thin_tac "flatten (normalize bdy) = P" for P)
  apply (drule flatten_normalize)
  apply (case_tac lista)
  apply  simp
  apply simp
  done

lemma normalize_call [simp]: 
  "normalize (call init ei p return er c) = call init ei p return er (\<lambda>i t. normalize (c i t))"
  by (simp add: call_def)

lemma normalize_dynCall [simp]:
  "normalize (dynCall init ei p return er c) = 
    dynCall init ei p return er (\<lambda>s t. normalize (c s t))" 
  by (simp add: dynCall_def)

lemma normalize_fcall [simp]:
  "normalize (fcall init ei p return er result c) = 
    fcall init ei p return er result (\<lambda>v. normalize (c v))"
  by (simp add: fcall_def)

lemma normalize_switch [simp]:
  "normalize (switch v Vcs) = switch v (map (\<lambda>(V,c). (V,normalize c)) Vcs)"
apply (induct Vcs)
apply auto
done

lemma normalize_guaranteeStrip [simp]:
  "normalize (guaranteeStrip f g c) = guaranteeStrip f g (normalize c)"
  by (simp add: guaranteeStrip_def)

lemma normalize_guards [simp]:
  "normalize (guards gs c) = guards gs (normalize c)"
  by (induct gs) auto

text {* Sequencial composition with guards in the body is not preserved by
        normalize *}
lemma normalize_while [simp]:
  "normalize (while gs b c) = guards gs
      (While b (sequence Seq (flatten (normalize c) @ flatten (guards gs Skip))))" 
  by (simp add: while_def)

lemma normalize_whileAnno [simp]:
  "normalize (whileAnno b I V c) = whileAnno b I V (normalize c)"
  by (simp add: whileAnno_def)

lemma normalize_whileAnnoG [simp]:
  "normalize (whileAnnoG gs b I V c) = guards gs
      (While b (sequence Seq (flatten (normalize c) @ flatten (guards gs Skip))))" 
  by (simp add: whileAnnoG_def)

lemma normalize_specAnno [simp]:
  "normalize (specAnno P c Q A) = specAnno P (\<lambda>s. normalize (c undefined)) Q A"
  by (simp add: specAnno_def)

lemmas normalize_simps = 
  normalize.simps normalize_raise normalize_condCatch normalize_bind
  normalize_block normalize_call normalize_dynCall normalize_fcall normalize_switch
  normalize_guaranteeStrip normalize_guards 
  normalize_while normalize_whileAnno normalize_whileAnnoG normalize_specAnno

lemma flattenc_raise [simp]: "flattenc (raise f e) = [Seq (Basic f e) Throw]"
  by (simp add: raise_def)

lemma flattenc_condCatch [simp]: "flattenc (condCatch c1 b c2) = flattenc c1 @ [Cond b c2 Throw]"
  by (simp add: condCatch_def)

lemma flattenc_bind [simp]: "flattenc (bind e c) = [bind e c]"
  by (simp add: bind_def)

lemma flattenc_bseq [simp]: "flattenc (bseq c1 c2) = [Seq c1 c2]"
  by (simp add: bseq_def)

lemma flattenc_block [simp]:
  "flattenc (block init ei bdy return er result) = [block init ei bdy return er result]"
  by (simp add: block_def)

lemma flattenc_call [simp]: "flattenc (call init ei p return er result) = [call init ei p return er result]"
  by (simp add: call_def)

lemma flattenc_dynCall [simp]: "flattenc (dynCall init ei p return er result) = [dynCall init ei p return er result]"
  by (simp add: dynCall_def)

lemma flattenc_fcall [simp]: "flattenc (fcall init ei p return er result c) = [fcall init ei p return er result c]"
  by (simp add: fcall_def)

lemma flattenc_switch [simp]: "flattenc (switch v Vcs) = [switch v Vcs]"
  by (cases Vcs) auto

lemma flattenc_guaranteeStrip [simp]: 
  "flattenc (guaranteeStrip f g c) = [guaranteeStrip f g c]"
  by (simp add: guaranteeStrip_def)

lemma flattenc_while [simp]: "flattenc (while gs b c) = [while gs b c]"
  apply (simp add: while_def)
  apply (induct gs)
  apply  auto
  done

lemma flattenc_whileAnno [simp]: 
  "flattenc (whileAnno b I V c) = [whileAnno b I V c]"
  by (simp add: whileAnno_def)

lemma flattenc_whileAnnoG [simp]: 
  "flattenc (whileAnnoG gs b I V c) = [whileAnnoG gs b I V c]"
  by (simp add: whileAnnoG_def)

lemma flattenc_specAnno [simp]:
  "flattenc (specAnno P c Q A) = flattenc (c undefined)"
  by (simp add: specAnno_def)

lemmas flattenc_simps = flattenc.simps  flattenc_condCatch flattenc_bind
  flattenc_block flattenc_call flattenc_dynCall flattenc_fcall flattenc_switch
  flattenc_guaranteeStrip
  flattenc_while flattenc_whileAnno flattenc_whileAnnoG flattenc_specAnno

lemma normalizec_raise:
 "normalizec (raise f e) = raise f e"
  by (simp add: raise_def)

lemma normalizec_condCatch:
 "normalizec (condCatch c1 b c2) = sequence Catch ((flattenc (normalizec c1))@ [Cond b (normalizec c2) Throw])"
  by (simp add: condCatch_def)

lemma normalizec_bind:
 "normalizec (bind e c) = bind e (\<lambda>v. normalizec (c v))"
  by (simp add: bind_def)

lemma normalizec_bseq:
 "normalizec (bseq c1 c2) =  bseq (normalizec c1)  (normalizec c2)"
  by (simp add: bseq_def)

lemma normalizec_block: "normalizec (block init ei bdy return er c) = 
                         block init ei (normalizec bdy) return er (\<lambda>s t. normalizec (c s t))"
  by (simp add: block_def )

lemma normalizec_call: 
  "normalizec (call init ei p return er c) = call init ei p return er (\<lambda>i t. normalizec (c i t))"
  by (simp add: call_def normalizec_block)

lemma normalizec_dynCall:
  "normalizec (dynCall init ei p return er c) = 
    dynCall init ei p return er (\<lambda>s t. normalizec (c s t))" 
  by (simp add: dynCall_def normalizec_call)

lemma normalizec_fcall:
  "normalizec (fcall init ei p return er result c) = 
    fcall init ei p return er result (\<lambda>v. normalizec (c v))"
  by (simp add: fcall_def normalizec_call)

lemma normalizec_switch:
  "normalizec (switch v Vcs) = switch v (map (\<lambda>(V,c). (V,normalizec c)) Vcs)"
apply (induct Vcs)
apply auto
done

lemma normalizec_guaranteeStrip:
  "normalizec (guaranteeStrip f g c) = guaranteeStrip f g (normalizec c)"
  by (simp add: guaranteeStrip_def)

lemma normalizec_guards:
  "normalizec (guards gs c) = guards gs (normalizec c)"
  by (induct gs) auto

text {* Sequencial composition with guards in the body is not preserved by
        normalize *}
lemma normalizec_while:
  "normalizec (while gs b c) = guards gs
      (While b (Seq  (normalizec c)  (guards gs Skip)))" 
  by (simp add: while_def normalizec_guards)

lemma normalizec_whileAnno:
  "normalizec (whileAnno b I V c) = whileAnno b I V (normalizec c)"
  by (simp add: whileAnno_def)

lemma normalizec_whileAnnoG :
  "normalizec (whileAnnoG gs b I V c) = guards gs
      (While b (Seq (normalizec c) (guards gs Skip)))" 
  by (simp add: whileAnnoG_def normalizec_while)

lemma normalizec_specAnno:
  "normalizec (specAnno P c Q A) = specAnno P (\<lambda>s. normalizec (c undefined)) Q A"
  by (simp add: specAnno_def)

(* lemmas normalizec_simps = 
  normalizec.simps normalizec_raise normalizec_condCatch normalizec_bind
  normalizec_block normalizec_call normalizec_dynCall normalizec_fcall normalizec_switch
  normalizec_guaranteeStrip normalizec_guards 
  normalizec_while normalizec_whileAnno normalizec_whileAnnoG normalizec_specAnno*)

subsubsection {* Stripping Guards: @{text "strip_guards"} *}

primrec strip_guards:: "'f set \<Rightarrow> ('s, 'p, 'f, 'e) com \<Rightarrow> ('s, 'p, 'f, 'e) com"
where
"strip_guards F Skip = Skip" |
"strip_guards F (Basic f e) = Basic f e" |
"strip_guards F (Spec r e) = Spec r e" |
"strip_guards F (Seq c\<^sub>1 c\<^sub>2)  = (Seq (strip_guards F c\<^sub>1) (strip_guards F c\<^sub>2))" |
"strip_guards F (Cond b c\<^sub>1 c\<^sub>2) = Cond b (strip_guards F c\<^sub>1) (strip_guards F c\<^sub>2)" |
"strip_guards F (While b c) = While b (strip_guards F c)" |
"strip_guards F (Call p) = Call p" |
"strip_guards F (DynCom c) = DynCom (\<lambda>s. (strip_guards F (c s)))" |
"strip_guards F (Guard f g c) = (if f \<in> F then strip_guards F c
                                  else Guard f g (strip_guards F c))" |
"strip_guards F Throw = Throw" |
"strip_guards F (Catch c\<^sub>1 c\<^sub>2) = Catch (strip_guards F c\<^sub>1) (strip_guards F c\<^sub>2)" |
"strip_guards F (Await b ca e) = Await b (Language.strip_guards F ca) e"

lemma no_await_strip_guards_eq: 
    assumes noawaits:"noawaits t"
    shows  "(Language.strip_guards F (sequential t)) = (sequential (strip_guards F t))"
using noawaits
by (induct t) auto


definition strip:: "'f set \<Rightarrow> 
                   ('p \<Rightarrow> ('s, 'p, 'f, 'e) com option) \<Rightarrow> ('p \<Rightarrow> ('s, 'p, 'f, 'e) com option)"
  where "strip F \<Gamma> = (\<lambda>p. map_option (strip_guards F) (\<Gamma> p))"



lemma strip_simp [simp]: "(strip F \<Gamma>) p = map_option (strip_guards F) (\<Gamma> p)"
  by (simp add: strip_def)

lemma dom_strip: "dom (strip F \<Gamma>) = dom \<Gamma>"
  by (auto)

lemma strip_guards_idem: "strip_guards F (strip_guards F c) = strip_guards F c"
  by (induct c) (auto simp add:Language.strip_guards_idem)

lemma strip_idem: "strip F (strip F \<Gamma>) = strip F \<Gamma>"
  apply (rule ext)
  apply (case_tac "\<Gamma> x")
  apply (auto simp add: strip_guards_idem strip_def)
  done

lemma strip_guards_raise [simp]:
  "strip_guards F (raise f e) = raise f e"
  by (simp add: raise_def)

lemma strip_guards_condCatch [simp]:
  "strip_guards F (condCatch c1 b c2) = 
    condCatch (strip_guards F c1) b (strip_guards F c2)"
  by (simp add: condCatch_def)

lemma strip_guards_bind [simp]:
  "strip_guards F (bind e c) = bind e (\<lambda>v. strip_guards F (c v))"
  by (simp add: bind_def)

lemma strip_guards_bseq [simp]:
  "strip_guards F (bseq c1 c2) = bseq (strip_guards F c1) (strip_guards F c2)"
  by (simp add: bseq_def)

lemma strip_guards_block [simp]:
  "strip_guards F (block init ei bdy return er c) =
    block init ei (strip_guards F bdy) return er (\<lambda>s t. strip_guards F (c s t))"
  by (simp add: block_def)

lemma strip_guards_call [simp]:
  "strip_guards F (call init ei p return er c) =
     call init ei p return er (\<lambda>s t. strip_guards F (c s t))"
  by (simp add: call_def)

lemma strip_guards_dynCall [simp]:
  "strip_guards F (dynCall init ei p return er c) =
     dynCall init ei p return er (\<lambda>s t. strip_guards F (c s t))"
  by (simp add: dynCall_def)

lemma strip_guards_fcall [simp]:
  "strip_guards F (fcall init ei p return er result c) =
     fcall init ei p return er result (\<lambda>v. strip_guards F (c v))"
  by (simp add: fcall_def)

lemma strip_guards_switch [simp]:
  "strip_guards F (switch v Vc) =
    switch v (map (\<lambda>(V,c). (V,strip_guards F c)) Vc)"
  by (induct Vc) auto

lemma strip_guards_guaranteeStrip [simp]:
  "strip_guards F (guaranteeStrip f g c) = 
    (if f \<in> F then strip_guards F c 
     else guaranteeStrip f g (strip_guards F c))"
  by (simp add: guaranteeStrip_def)

lemma guaranteeStripPair_split_conv [simp]: "case_prod c (guaranteeStripPair f g) = c f g"
  by (simp add: guaranteeStripPair_def)

lemma strip_guards_guards [simp]: "strip_guards F (guards gs c) =
        guards (filter (\<lambda>(f,g). f \<notin> F) gs) (strip_guards F c)"
  by (induct gs) auto

lemma strip_guards_while [simp]:
 "strip_guards F (while gs b  c) = 
     while (filter (\<lambda>(f,g). f \<notin> F) gs) b (strip_guards F c)"
  by (simp add: while_def)

lemma strip_guards_whileAnno [simp]:
 "strip_guards F (whileAnno b I V c) = whileAnno b I V (strip_guards F c)"
  by (simp add: whileAnno_def  while_def)

lemma strip_guards_whileAnnoG [simp]:
 "strip_guards F (whileAnnoG gs b I V c) = 
     whileAnnoG (filter (\<lambda>(f,g). f \<notin> F) gs) b I V (strip_guards F c)"
  by (simp add: whileAnnoG_def)

lemma strip_guards_specAnno [simp]:
  "strip_guards F (specAnno P c Q A) = 
    specAnno P (\<lambda>s. strip_guards F (c undefined)) Q A"
  by (simp add: specAnno_def)

lemmas strip_guards_simps = strip_guards.simps strip_guards_raise 
  strip_guards_condCatch strip_guards_bind strip_guards_bseq strip_guards_block
  strip_guards_dynCall strip_guards_fcall strip_guards_switch 
  strip_guards_guaranteeStrip guaranteeStripPair_split_conv strip_guards_guards
  strip_guards_while strip_guards_whileAnno strip_guards_whileAnnoG
  strip_guards_specAnno

subsubsection {* Marking Guards: @{text "mark_guards"} *}

primrec mark_guards:: "'f \<Rightarrow> ('s,'p,'g, 'e) com \<Rightarrow> ('s, 'p, 'f, 'e) com"
where
"mark_guards f Skip = Skip" |
"mark_guards f (Basic g e) = Basic g e" |
"mark_guards f (Spec r e) = Spec r e" |
"mark_guards f (Seq c\<^sub>1 c\<^sub>2)  = (Seq (mark_guards f c\<^sub>1) (mark_guards f c\<^sub>2))" |
"mark_guards f (Cond b c\<^sub>1 c\<^sub>2) = Cond b (mark_guards f c\<^sub>1) (mark_guards f c\<^sub>2)" |
"mark_guards f (While b c) = While b (mark_guards f c)" |
"mark_guards f (Call p) = Call p" |
"mark_guards f (DynCom c) = DynCom (\<lambda>s. (mark_guards f (c s)))" |
"mark_guards f (Guard f' g c) = Guard f g (mark_guards f c)" |
"mark_guards f Throw = Throw" |
"mark_guards f (Catch c\<^sub>1 c\<^sub>2) = Catch (mark_guards f c\<^sub>1) (mark_guards f c\<^sub>2)" |
"mark_guards f (Await b ca e) = Await b (Language.mark_guards f ca) e"

lemma mark_guards_raise: "mark_guards f (raise g e) = raise g e"
  by (simp add: raise_def)

lemma mark_guards_condCatch [simp]:
  "mark_guards f (condCatch c1 b c2) = 
    condCatch (mark_guards f c1) b (mark_guards f c2)"
  by (simp add: condCatch_def)

lemma mark_guards_bind [simp]:
  "mark_guards f (bind e c) = bind e (\<lambda>v. mark_guards f (c v))"
  by (simp add: bind_def)

lemma mark_guards_bseq [simp]:
  "mark_guards f (bseq c1 c2) = bseq (mark_guards f c1) (mark_guards f c2)"
  by (simp add: bseq_def)

lemma mark_guards_block [simp]:
  "mark_guards f (block init ei bdy return er c) =
    block init ei (mark_guards f bdy) return er (\<lambda>s t. mark_guards f (c s t))"
  by (simp add: block_def)

lemma mark_guards_call [simp]:
  "mark_guards f (call init ei p return er c) =
     call init ei p return er (\<lambda>s t. mark_guards f (c s t))"
  by (simp add: call_def)

lemma mark_guards_dynCall [simp]:
  "mark_guards f (dynCall init ei p return er c) =
     dynCall init ei p return er (\<lambda>s t. mark_guards f (c s t))"
  by (simp add: dynCall_def)

lemma mark_guards_fcall [simp]:
  "mark_guards f (fcall init ei p return er result c) =
     fcall init ei p return er result (\<lambda>v. mark_guards f (c v))"
  by (simp add: fcall_def)

lemma mark_guards_switch [simp]: 
  "mark_guards f (switch v vs) = 
     switch v (map (\<lambda>(V,c). (V,mark_guards f c)) vs)"
  by (induct vs) auto

lemma mark_guards_guaranteeStrip [simp]:
  "mark_guards f (guaranteeStrip f' g c) = guaranteeStrip f g (mark_guards f c)"
  by (simp add: guaranteeStrip_def)

lemma mark_guards_guards [simp]: 
  "mark_guards f (guards gs c) = guards (map (\<lambda>(f',g). (f,g)) gs) (mark_guards f c)"
  by (induct gs) auto

lemma mark_guards_while [simp]:
 "mark_guards f (while gs b c) = 
    while (map (\<lambda>(f',g). (f,g)) gs) b (mark_guards f c)"
  by (simp add: while_def) 

lemma mark_guards_whileAnno [simp]:
 "mark_guards f (whileAnno b I V c) = whileAnno b I V (mark_guards f c)"
  by (simp add: whileAnno_def while_def)

lemma mark_guards_whileAnnoG [simp]:
 "mark_guards f (whileAnnoG gs b I V c) = 
    whileAnnoG (map (\<lambda>(f',g). (f,g)) gs) b I V (mark_guards f c)"
  by (simp add: whileAnno_def whileAnnoG_def while_def) 

lemma mark_guards_specAnno [simp]:
  "mark_guards f (specAnno P c Q A) = 
    specAnno P (\<lambda>s. mark_guards f (c undefined)) Q A"
  by (simp add: specAnno_def)

lemmas mark_guards_simps = mark_guards.simps mark_guards_raise 
  mark_guards_condCatch mark_guards_bind mark_guards_bseq mark_guards_block
  mark_guards_dynCall mark_guards_fcall mark_guards_switch 
  mark_guards_guaranteeStrip guaranteeStripPair_split_conv mark_guards_guards
  mark_guards_while mark_guards_whileAnno mark_guards_whileAnnoG
  mark_guards_specAnno

definition is_Guard:: "('s, 'p, 'f, 'e) com \<Rightarrow> bool"
  where "is_Guard c = (case c of Guard f g c' \<Rightarrow> True | _ \<Rightarrow> False)"
lemma is_Guard_basic_simps [simp]:
 "is_Guard Skip = False"
 "is_Guard (Basic f ev) = False"
 "is_Guard (Spec r ev) = False"
 "is_Guard (Seq c1 c2) = False"
 "is_Guard (Cond b c1 c2) = False"
 "is_Guard (While b c) = False"
 "is_Guard (Call p) = False"
 "is_Guard (DynCom C) = False"
 "is_Guard (Guard F g c) = True"
 "is_Guard (Throw) = False"
 "is_Guard (Catch c1 c2) = False"
 "is_Guard (raise f ev) = False"
 "is_Guard (condCatch c1 b c2) = False"
 "is_Guard (bind e cv) = False"
 "is_Guard (bseq c1 c2) = False"
 "is_Guard (block init ei bdy return er cont) = False"
 "is_Guard (call init ei p return er cont) = False"
 "is_Guard (dynCall init ei P return er cont) = False"
 "is_Guard (fcall init ei p return er result cont') = False"
 "is_Guard (whileAnno b I V c) = False"
 "is_Guard (guaranteeStrip F g c) = True"
 "is_Guard (Await b ca ev) = False"
  by (auto simp add: is_Guard_def raise_def condCatch_def bind_def bseq_def
          block_def call_def dynCall_def fcall_def whileAnno_def guaranteeStrip_def)


lemma is_Guard_switch [simp]:
 "is_Guard (switch v Vc) = False"
  by (induct Vc) auto

lemmas is_Guard_simps = is_Guard_basic_simps is_Guard_switch

primrec dest_Guard:: "('s, 'p, 'f, 'e) com \<Rightarrow> ('f \<times> 's set \<times> ('s, 'p, 'f, 'e) com)"
  where "dest_Guard (Guard f g c) = (f,g,c)"

lemma dest_Guard_guaranteeStrip [simp]: "dest_Guard (guaranteeStrip f g c) = (f,g,c)"
  by (simp add: guaranteeStrip_def)

lemmas dest_Guard_simps = dest_Guard.simps dest_Guard_guaranteeStrip

subsubsection {* Merging Guards: @{text merge_guards}*}

primrec merge_guards:: "('s, 'p, 'f, 'e) com \<Rightarrow> ('s, 'p, 'f, 'e) com"
where
"merge_guards Skip = Skip" |
"merge_guards (Basic g e) = Basic g e" |
"merge_guards (Spec r e) = Spec r e" |
"merge_guards (Seq c\<^sub>1 c\<^sub>2)  = (Seq (merge_guards c\<^sub>1) (merge_guards c\<^sub>2))" |
"merge_guards (Cond b c\<^sub>1 c\<^sub>2) = Cond b (merge_guards c\<^sub>1) (merge_guards c\<^sub>2)" |
"merge_guards (While b c) = While b (merge_guards c)" |
"merge_guards (Call p) = Call p" |
"merge_guards (DynCom c) = DynCom (\<lambda>s. (merge_guards (c s)))" |
"merge_guards (Await b ca e) = Await b (Language.merge_guards ca) e" |
(*"merge_guards (Guard f g c) = 
    (case (merge_guards c) of
      Guard f' g' c' \<Rightarrow> if f=f' then Guard f (g \<inter> g') c' 
                        else Guard f g (Guard f' g' c')
     | _ \<Rightarrow>  Guard f g (merge_guards c))"*)
(* the following version works better with derived language constructs *)
"merge_guards (Guard f g c) = 
    (let c' = (merge_guards c)
     in if is_Guard c' 
        then let (f',g',c'') = dest_Guard c' 
             in if f=f' then Guard f (g \<inter> g') c'' 
                        else Guard f g (Guard f' g' c'')
        else Guard f g c')" |
"merge_guards Throw = Throw" |
"merge_guards (Catch c\<^sub>1 c\<^sub>2) = Catch (merge_guards c\<^sub>1) (merge_guards c\<^sub>2)"

lemma merge_guards_res_Skip: "merge_guards c = Skip \<Longrightarrow> c = Skip"
  by (cases c) (auto split: com.splits if_split_asm simp add: is_Guard_def Let_def)

lemma merge_guards_res_Basic: "merge_guards c = Basic f e \<Longrightarrow> c = Basic f e"
  by (cases c) (auto split: com.splits if_split_asm simp add: is_Guard_def Let_def)

lemma merge_guards_res_Spec: "merge_guards c = Spec r e \<Longrightarrow> c = Spec r e"
  by (cases c) (auto split: com.splits if_split_asm simp add: is_Guard_def Let_def)

lemma merge_guards_res_Seq: "merge_guards c = Seq c1 c2 \<Longrightarrow> 
    \<exists>c1' c2'. c = Seq c1' c2' \<and> merge_guards c1' = c1 \<and> merge_guards c2' = c2"
  by (cases c) (auto split: com.splits if_split_asm simp add: is_Guard_def Let_def)

lemma merge_guards_res_Cond: "merge_guards c = Cond b c1 c2 \<Longrightarrow> 
    \<exists>c1' c2'. c = Cond b c1' c2' \<and> merge_guards c1' = c1 \<and> merge_guards c2' = c2"
  by (cases c) (auto split: com.splits if_split_asm simp add: is_Guard_def Let_def)

lemma merge_guards_res_While: "merge_guards c = While b c' \<Longrightarrow> 
    \<exists>c''. c = While b c''  \<and> merge_guards c'' = c'"
  by (cases c) (auto split: com.splits if_split_asm simp add: is_Guard_def Let_def)

lemma merge_guards_res_Call: "merge_guards c = Call p \<Longrightarrow> c = Call p"
  by (cases c) (auto split: com.splits if_split_asm simp add: is_Guard_def Let_def)

lemma merge_guards_res_DynCom: "merge_guards c = DynCom c' \<Longrightarrow> 
    \<exists>c''. c = DynCom c''  \<and> (\<lambda>s. (merge_guards (c'' s))) = c'"
  by (cases c) (auto split: com.splits if_split_asm simp add: is_Guard_def Let_def)

lemma merge_guards_res_Throw: "merge_guards c = Throw \<Longrightarrow> c = Throw"
  by (cases c) (auto split: com.splits if_split_asm simp add: is_Guard_def Let_def)

lemma merge_guards_res_Catch: "merge_guards c = Catch c1 c2 \<Longrightarrow> 
    \<exists>c1' c2'. c = Catch c1' c2' \<and> merge_guards c1' = c1 \<and> merge_guards c2' = c2"
  by (cases c) (auto split: com.splits if_split_asm simp add: is_Guard_def Let_def)

lemma merge_guards_res_Guard: 
 "merge_guards c = Guard f g c' \<Longrightarrow> \<exists>c'' f' g'. c = Guard f' g' c''"
  by (cases c) (auto split: com.splits if_split_asm simp add: is_Guard_def Let_def)

lemma merge_guards_res_Await: "merge_guards c = Await b c' e \<Longrightarrow> 
      \<exists>c''. c = Await b c'' e \<and> Language.merge_guards c'' = c'"
  by (cases c) (auto split: com.splits if_split_asm simp add: is_Guard_def Let_def)


lemmas merge_guards_res_simps = merge_guards_res_Skip merge_guards_res_Basic 
 merge_guards_res_Spec merge_guards_res_Seq merge_guards_res_Cond 
 merge_guards_res_While merge_guards_res_Call
 merge_guards_res_DynCom merge_guards_res_Throw merge_guards_res_Catch 
 merge_guards_res_Guard merge_guards_res_Await

lemma merge_guards_raise: "merge_guards (raise g e) = raise g e"
  by (simp add: raise_def)

lemma merge_guards_condCatch [simp]:
  "merge_guards (condCatch c1 b c2) = 
    condCatch (merge_guards c1) b (merge_guards c2)"
  by (simp add: condCatch_def)

lemma merge_guards_bind [simp]:
  "merge_guards (bind e c) = bind e (\<lambda>v. merge_guards (c v))"
  by (simp add: bind_def)

lemma merge_guards_bseq [simp]:
  "merge_guards (bseq c1 c2) = bseq (merge_guards c1) (merge_guards c2)"
  by (simp add: bseq_def)

lemma merge_guards_block [simp]:
  "merge_guards (block init ei bdy return er c) =
    block init ei (merge_guards bdy) return er (\<lambda>s t. merge_guards (c s t))"
  by (simp add: block_def)

lemma merge_guards_call [simp]:
  "merge_guards (call init ei p return er c) =
     call init ei p return er (\<lambda>s t. merge_guards (c s t))"
  by (simp add: call_def)

lemma merge_guards_dynCall [simp]:
  "merge_guards (dynCall init ei p return er c) =
     dynCall init ei p return er (\<lambda>s t. merge_guards (c s t))"
  by (simp add: dynCall_def)

lemma merge_guards_fcall [simp]:
  "merge_guards (fcall init ei p return er result c) =
     fcall init ei p return er result (\<lambda>v. merge_guards (c v))"
  by (simp add: fcall_def)

lemma merge_guards_switch [simp]: 
  "merge_guards (switch v vs) = 
     switch v (map (\<lambda>(V,c). (V,merge_guards c)) vs)"
  by (induct vs) auto

lemma merge_guards_guaranteeStrip [simp]: 
  "merge_guards (guaranteeStrip f g c) = 
    (let c' = (merge_guards c)
     in if is_Guard c' 
        then let (f',g',c') = dest_Guard c' 
             in if f=f' then Guard f (g \<inter> g') c' 
                        else Guard f g (Guard f' g' c')
        else Guard f g c')"
  by (simp add: guaranteeStrip_def)

lemma merge_guards_whileAnno [simp]:
 "merge_guards (whileAnno b I V c) = whileAnno b I V (merge_guards c)"
  by (simp add: whileAnno_def while_def)

lemma merge_guards_specAnno [simp]:
  "merge_guards (specAnno P c Q A) = 
    specAnno P (\<lambda>s. merge_guards (c undefined)) Q A"
  by (simp add: specAnno_def)

text {* @{term "merge_guards"} for guard-lists as in @{const guards}, @{const while}
 and @{const whileAnnoG} may have funny effects since the guard-list has to
 be merged with the body statement too.*}

lemmas merge_guards_simps = merge_guards.simps merge_guards_raise 
  merge_guards_condCatch merge_guards_bind merge_guards_bseq merge_guards_block
  merge_guards_dynCall merge_guards_fcall merge_guards_switch 
  merge_guards_guaranteeStrip merge_guards_whileAnno merge_guards_specAnno

primrec noguards:: "('s, 'p, 'f, 'e) com \<Rightarrow> bool"
where
"noguards Skip = True" |
"noguards (Basic f e) = True" |
"noguards (Spec r e ) = True" |
"noguards (Seq c\<^sub>1 c\<^sub>2)  = (noguards c\<^sub>1 \<and> noguards c\<^sub>2)" |
"noguards (Cond b c\<^sub>1 c\<^sub>2) = (noguards c\<^sub>1 \<and> noguards c\<^sub>2)" |
"noguards (While b c) = (noguards c)" |
"noguards (Call p) = True" |
"noguards (DynCom c) = (\<forall>s. noguards (c s))" |
"noguards (Guard f g c) = False" |
"noguards Throw = True" |
"noguards (Catch c\<^sub>1 c\<^sub>2) = (noguards c\<^sub>1 \<and> noguards c\<^sub>2)" |
"noguards (Await b c e) = (Language.noguards c) "

lemma noawaits_noguards_seq:"noawaits c \<Longrightarrow> noguards c = Language.noguards (sequential c)"
by (induct c, auto)

lemma noguards_strip_guards: "noguards (strip_guards UNIV c)"
  by (induct c) (auto simp add: noguards_strip_guards)

primrec nothrows:: "('s, 'p, 'f, 'e) com \<Rightarrow> bool"
where
"nothrows Skip = True" |
"nothrows (Basic f e) = True" |
"nothrows (Spec r e) = True" |
"nothrows (Seq c\<^sub>1 c\<^sub>2)  = (nothrows c\<^sub>1 \<and> nothrows c\<^sub>2)" |
"nothrows (Cond b c\<^sub>1 c\<^sub>2) = (nothrows c\<^sub>1 \<and> nothrows c\<^sub>2)" |
"nothrows (While b c) = nothrows c" |
"nothrows (Call p) = True" |
"nothrows (DynCom c) = (\<forall>s. nothrows (c s))" |
"nothrows (Guard f g c) = nothrows c" |
"nothrows Throw = False" |
"nothrows (Catch c\<^sub>1 c\<^sub>2) = (nothrows c\<^sub>1 \<and> nothrows c\<^sub>2)" |
"nothrows (Await b cn e) = Language.nothrows cn"

lemma noawaits_nothrows_seq:"noawaits c \<Longrightarrow> nothrows c = Language.nothrows (sequential c)"
by (induct c, auto)

subsubsection {* Intersecting Guards: @{text "c\<^sub>1 \<inter>\<^sub>g c\<^sub>2"}*}

inductive_set com_rel ::"(('s, 'p, 'f, 'e) com \<times> ('s, 'p, 'f, 'e) com) set"
where
  "(c1, Seq c1 c2) \<in> com_rel"
| "(c2, Seq c1 c2) \<in> com_rel"
| "(c1, Cond b c1 c2) \<in> com_rel"
| "(c2, Cond b c1 c2) \<in> com_rel"
| "(c, While b c) \<in> com_rel"
| "(c x, DynCom c) \<in> com_rel"
| "(c, Guard f g c) \<in> com_rel"
| "(c1, Catch c1 c2) \<in> com_rel"
| "(c2, Catch c1 c2) \<in> com_rel"
 


inductive_cases com_rel_elim_cases:
 "(c, Skip) \<in> com_rel"
 "(c, Basic f e) \<in> com_rel"
 "(c, Spec r e) \<in> com_rel"
 "(c, Seq c1 c2) \<in> com_rel"
 "(c, Cond b c1 c2) \<in> com_rel"
 "(c, While b c1) \<in> com_rel"
 "(c, Call p) \<in> com_rel"
 "(c, DynCom c1) \<in> com_rel"
 "(c, Guard f g c1) \<in> com_rel"
 "(c, Throw) \<in> com_rel"
 "(c, Catch c1 c2) \<in> com_rel" 
 "(c, Await b cn e) \<in> com_rel"


lemma wf_com_rel: "wf com_rel"
apply (rule wfUNIVI)
apply (induct_tac x)
apply            (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases)
apply           (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases)
apply          (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases)
apply         (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases,
                simp,simp)
apply        (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases,
               simp,simp)
apply       (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases,simp)
apply      (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases)
apply     (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases,simp)
apply    (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases,simp)
apply   (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases)
apply  (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases,simp,simp)
apply (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases)
done

consts inter_guards:: "('s, 'p, 'f, 'e) com \<times> ('s, 'p, 'f, 'e) com \<Rightarrow> ('s, 'p, 'f, 'e) com option"

abbreviation 
  inter_guards_syntax :: "('s,'p,'f,'e) LanguageCon.com \<Rightarrow> ('s,'p,'f,'e) LanguageCon.com \<Rightarrow> ('s,'p,'f,'e) LanguageCon.com option"
           ("_ \<inter>\<^sub>g\<^sub>s _" [20,20] 19)
  where "((c::('s, 'p, 'f, 'e) com) \<inter>\<^sub>g\<^sub>s (d::('s, 'p, 'f, 'e) com)) == LanguageCon.inter_guards (c,d)" 

recdef inter_guards "inv_image com_rel fst" 
"(Skip \<inter>\<^sub>g\<^sub>s Skip) = Some Skip"

"(Basic f1 e1 \<inter>\<^sub>g\<^sub>s Basic f2 e2) = (if (f1=f2) \<and> (e1=e2) then Some (Basic f1 e1) else None)"
"(Spec r1 e1 \<inter>\<^sub>g\<^sub>s Spec r2 e2) = (if (r1=r2) \<and> (e1=e2) then Some (Spec r1 e1) else None)"
"(Seq a1 a2 \<inter>\<^sub>g\<^sub>s Seq b1 b2) = 
   (case (a1 \<inter>\<^sub>g\<^sub>s b1) of
      None \<Rightarrow> None
    | Some c1 \<Rightarrow> (case (a2 \<inter>\<^sub>g\<^sub>s b2) of
                    None \<Rightarrow> None
                  | Some c2 \<Rightarrow> Some (Seq c1 c2)))"

"(Cond cnd1 t1 e1 \<inter>\<^sub>g\<^sub>s Cond cnd2 t2 e2) = 
   (if (cnd1=cnd2) 
    then (case (t1 \<inter>\<^sub>g\<^sub>s t2) of 
            None \<Rightarrow> None
          | Some t \<Rightarrow> (case (e1 \<inter>\<^sub>g\<^sub>s e2) of
                         None \<Rightarrow> None
                       | Some e \<Rightarrow> Some (Cond cnd1 t e)))
    else None)"

"(While cnd1 c1 \<inter>\<^sub>g\<^sub>s While cnd2 c2) = 
    (if (cnd1=cnd2 )
     then (case (c1 \<inter>\<^sub>g\<^sub>s c2) of
             None \<Rightarrow> None
           | Some c \<Rightarrow> Some (While cnd1 c))
     else None)"

"(Call p1 \<inter>\<^sub>g\<^sub>s Call p2) = 
   (if p1 = p2
    then Some (Call p1)
    else None)"

"(DynCom P1 \<inter>\<^sub>g\<^sub>s DynCom P2) = 
   (if (\<forall>s. ((P1 s) \<inter>\<^sub>g\<^sub>s (P2 s)) \<noteq> None)
   then Some (DynCom (\<lambda>s.  the ((P1 s) \<inter>\<^sub>g\<^sub>s (P2 s))))
   else None)"

"(Guard m1 g1 c1 \<inter>\<^sub>g\<^sub>s Guard m2 g2 c2) = 
   (if m1=m2 then
       (case (c1 \<inter>\<^sub>g\<^sub>s c2) of
          None \<Rightarrow> None
        | Some c \<Rightarrow> Some (Guard m1 (g1 \<inter> g2) c))
    else None)"

"(Throw \<inter>\<^sub>g\<^sub>s Throw) = Some Throw"
"(Catch a1 a2 \<inter>\<^sub>g\<^sub>s Catch b1 b2) = 
   (case (a1 \<inter>\<^sub>g\<^sub>s b1) of
      None \<Rightarrow> None
    | Some c1 \<Rightarrow> (case (a2 \<inter>\<^sub>g\<^sub>s b2) of
                    None \<Rightarrow> None
                  | Some c2 \<Rightarrow> Some (Catch c1 c2)))" 
"(Await cnd1 ca1 e1 \<inter>\<^sub>g\<^sub>s Await cnd2 ca2 e2) = 
 (if (cnd1=cnd2 \<and> e1=e2) then 
       (case (ca1 \<inter>\<^sub>g ca2) of
             None \<Rightarrow> None
           | Some c \<Rightarrow> Some (Await cnd1 c e1))
     else None)"

"(c \<inter>\<^sub>g\<^sub>s d) = None"

(hints cong add: option.case_cong if_cong  
       recdef_wf: wf_com_rel simp: com_rel.intros)

lemma inter_guards_strip_eq:
  "\<And>(c::('s, 'p, 'f, 'e) com). ((c1::('s, 'p, 'f, 'e) com) \<inter>\<^sub>g\<^sub>s (c2::('s, 'p, 'f, 'e) com)) = Some c  \<Longrightarrow> 
    (strip_guards UNIV c = strip_guards UNIV c1) \<and> 
    (strip_guards UNIV c = strip_guards UNIV c2)"
apply (induct c1 c2 rule: inter_guards.induct) 
prefer 8 
apply (simp split: if_split_asm)
apply hypsubst
apply simp
apply (rule ext)
apply (erule_tac x=s in allE, erule exE)
apply (erule_tac x=s in allE)
apply fastforce
apply (fastforce dest:inter_guards_strip_eq split: option.splits if_split_asm)+
done

lemma inter_guards_sym: "\<And>c. (c1 \<inter>\<^sub>g\<^sub>s c2) = Some c \<Longrightarrow> (c2 \<inter>\<^sub>g\<^sub>s c1) = Some c"
apply (induct c1 c2 rule: inter_guards.induct)
apply (simp_all)
prefer 7
apply (simp split: if_split_asm)
apply (rule conjI)
apply  (clarsimp)
apply  (rule ext)
apply  (erule_tac x=s in allE)+
apply (fastforce dest:inter_guards_sym split: option.splits if_split_asm)+
done


lemma inter_guards_Skip: "(Skip \<inter>\<^sub>g\<^sub>s c2) = Some c = (c2=Skip \<and> c=Skip)"
  by (cases c2) auto

lemma inter_guards_Basic: 
  "((Basic f e1) \<inter>\<^sub>g\<^sub>s c2) = Some c = (c2=Basic f e1 \<and> c=Basic f e1)"
  by (cases c2) auto

lemma inter_guards_Spec: 
  "((Spec r e1) \<inter>\<^sub>g\<^sub>s c2) = Some c = (c2=Spec r e1 \<and> c=Spec r e1)"
  by (cases c2) auto

lemma inter_guards_Seq: 
  "(Seq a1 a2 \<inter>\<^sub>g\<^sub>s c2) = Some c = 
     (\<exists>b1 b2 d1 d2. c2=Seq b1 b2 \<and> (a1 \<inter>\<^sub>g\<^sub>s b1) = Some d1 \<and> 
        (a2 \<inter>\<^sub>g\<^sub>s b2) = Some d2 \<and> c=Seq d1 d2)"
  by (cases c2) (auto split: option.splits)

lemma inter_guards_Cond:
  "(Cond cnd t1 e1 \<inter>\<^sub>g\<^sub>s c2) = Some c =
     (\<exists>t2 e2 t e. c2=Cond cnd t2 e2 \<and> (t1 \<inter>\<^sub>g\<^sub>s t2) = Some t \<and> 
        (e1 \<inter>\<^sub>g\<^sub>s e2) = Some e \<and> c=Cond cnd t e)"  
  by (cases c2) (auto split: option.splits)

lemma inter_guards_While:
 "(While cnd bdy1 \<inter>\<^sub>g\<^sub>s c2) = Some c =
     (\<exists>bdy2 bdy. c2 =While cnd bdy2 \<and> (bdy1 \<inter>\<^sub>g\<^sub>s bdy2) = Some bdy \<and>
       c=While cnd bdy)"
  by (cases c2) (auto split: option.splits if_split_asm)

lemma inter_guards_Await:
 "(Await cnd bdy1 e1 \<inter>\<^sub>g\<^sub>s c2) = Some c =
     (\<exists>bdy2 bdy. c2 =Await cnd bdy2 e1 \<and> (bdy1 \<inter>\<^sub>g bdy2) = Some bdy \<and>
       c=Await cnd bdy e1)"
  by (cases c2) (auto split: option.splits if_split_asm)

lemma inter_guards_Call:
  "(Call p \<inter>\<^sub>g\<^sub>s c2) = Some c =
     (c2=Call p \<and> c=Call p)"
  by (cases c2) (auto split: if_split_asm)

lemma inter_guards_DynCom:
  "(DynCom f1 \<inter>\<^sub>g\<^sub>s c2) = Some c =
     (\<exists>f2. c2=DynCom f2 \<and> (\<forall>s. ((f1 s) \<inter>\<^sub>g\<^sub>s (f2 s)) \<noteq> None) \<and>
      c=DynCom (\<lambda>s. the ((f1 s) \<inter>\<^sub>g\<^sub>s (f2 s))))"
  by (cases c2) (auto split: if_split_asm)


lemma inter_guards_Guard:
  "(Guard f g1 bdy1 \<inter>\<^sub>g\<^sub>s c2) = Some c =
     (\<exists>g2 bdy2 bdy. c2=Guard f g2 bdy2 \<and> (bdy1 \<inter>\<^sub>g\<^sub>s bdy2) = Some bdy \<and>
       c=Guard f (g1 \<inter> g2) bdy)" 
  by (cases c2) (auto split: option.splits)

lemma inter_guards_Throw:
  "(Throw \<inter>\<^sub>g\<^sub>s c2) = Some c = (c2=Throw \<and> c=Throw)"
  by (cases c2) auto

lemma inter_guards_Catch:
  "(Catch a1 a2 \<inter>\<^sub>g\<^sub>s c2) = Some c = 
     (\<exists>b1 b2 d1 d2. c2=Catch b1 b2 \<and> (a1 \<inter>\<^sub>g\<^sub>s b1) = Some d1 \<and> 
        (a2 \<inter>\<^sub>g\<^sub>s b2) = Some d2 \<and> c=Catch d1 d2)"
  by (cases c2) (auto split: option.splits)


lemmas inter_guards_simps = inter_guards_Skip inter_guards_Basic inter_guards_Spec
  inter_guards_Seq inter_guards_Cond inter_guards_While inter_guards_Call
  inter_guards_DynCom inter_guards_Guard inter_guards_Throw 
  inter_guards_Catch inter_guards_Await

subsubsection {* Subset on Guards: @{text "c\<^sub>1 \<subseteq>\<^sub>g c\<^sub>2"} *} 


consts subseteq_guards:: "('s, 'p, 'f, 'e) com \<times> ('s, 'p, 'f, 'e) com \<Rightarrow> bool"

abbreviation
  subseteq_guards_syntax :: "('s, 'p, 'f, 'e) com \<Rightarrow> ('s, 'p, 'f, 'e) com \<Rightarrow> bool"
           ("_ \<subseteq>\<^sub>g\<^sub>s _" [20,20] 19)
  where "c \<subseteq>\<^sub>g\<^sub>s d == subseteq_guards (c,d)"


recdef subseteq_guards "inv_image com_rel snd" 
"(Skip \<subseteq>\<^sub>g\<^sub>s Skip) = True"
"(Basic f1 e1 \<subseteq>\<^sub>g\<^sub>s Basic f2 e2) = ((f1=f2) \<and> (e1 = e2))"
"(Spec r1 e1 \<subseteq>\<^sub>g\<^sub>s Spec r2 e2) = ((r1=r2) \<and> (e1 = e2))"
"(Seq a1 a2 \<subseteq>\<^sub>g\<^sub>s Seq b1 b2) = ((a1 \<subseteq>\<^sub>g\<^sub>s b1) \<and> (a2 \<subseteq>\<^sub>g\<^sub>s b2))"
"(Cond cnd1 t1 e1 \<subseteq>\<^sub>g\<^sub>s Cond cnd2 t2 e2) = ((cnd1=cnd2) \<and> (t1 \<subseteq>\<^sub>g\<^sub>s t2) \<and> (e1 \<subseteq>\<^sub>g\<^sub>s e2))"
"(While cnd1 c1 \<subseteq>\<^sub>g\<^sub>s While cnd2 c2) = ((cnd1=cnd2) \<and> (c1 \<subseteq>\<^sub>g\<^sub>s c2))"
"(Call p1 \<subseteq>\<^sub>g\<^sub>s Call p2) = (p1 = p2)"
"(DynCom P1 \<subseteq>\<^sub>g\<^sub>s DynCom P2) = (\<forall>s. ((P1 s) \<subseteq>\<^sub>g\<^sub>s (P2 s)))"
"(Guard m1 g1 c1 \<subseteq>\<^sub>g\<^sub>s Guard m2 g2 c2) = 
    ((m1=m2 \<and> g1=g2 \<and> (c1 \<subseteq>\<^sub>g\<^sub>s c2)) \<or> (Guard m1 g1 c1 \<subseteq>\<^sub>g\<^sub>s c2))"
"(c1 \<subseteq>\<^sub>g\<^sub>s Guard m2 g2 c2) = (c1 \<subseteq>\<^sub>g\<^sub>s c2)"
"(Await cnd1 ca1 e1 \<subseteq>\<^sub>g\<^sub>s Await cnd2 ca2 e2) = ((cnd1=cnd2) \<and> (ca1 \<subseteq>\<^sub>g ca2) \<and> (e1=e2))"

"(Throw \<subseteq>\<^sub>g\<^sub>s Throw) = True"
"(Catch a1 a2 \<subseteq>\<^sub>g\<^sub>s Catch b1 b2) = ((a1 \<subseteq>\<^sub>g\<^sub>s b1) \<and> (a2 \<subseteq>\<^sub>g\<^sub>s b2))" 
"(c \<subseteq>\<^sub>g\<^sub>s d) = False"

(hints cong add: if_cong  
       recdef_wf: wf_com_rel simp: com_rel.intros)



lemma subseteq_guards_Skip:
 "c \<subseteq>\<^sub>g\<^sub>s Skip \<Longrightarrow> c = Skip"
  by (cases c) (auto)

lemma subseteq_guards_Basic:
 "c \<subseteq>\<^sub>g\<^sub>s Basic f e \<Longrightarrow> c = Basic f e"
  by (cases c) (auto)

lemma subseteq_guards_Spec:
 "c \<subseteq>\<^sub>g\<^sub>s Spec r e \<Longrightarrow> c = Spec r e"
  by (cases c) (auto)

lemma subseteq_guards_Seq:
  "c \<subseteq>\<^sub>g\<^sub>s Seq c1 c2 \<Longrightarrow> \<exists>c1' c2'. c=Seq c1' c2' \<and> (c1' \<subseteq>\<^sub>g\<^sub>s c1) \<and> (c2' \<subseteq>\<^sub>g\<^sub>s c2)"
  by (cases c) (auto)

lemma subseteq_guards_Cond:
  "c \<subseteq>\<^sub>g\<^sub>s Cond b c1 c2 \<Longrightarrow> \<exists>c1' c2'. c=Cond b c1' c2' \<and> (c1' \<subseteq>\<^sub>g\<^sub>s c1) \<and> (c2' \<subseteq>\<^sub>g\<^sub>s c2)"
  by (cases c) (auto)

lemma subseteq_guards_While:
  "c \<subseteq>\<^sub>g\<^sub>s While b c' \<Longrightarrow> \<exists>c''. c=While b c'' \<and> (c'' \<subseteq>\<^sub>g\<^sub>s c')"
  by (cases c) (auto)

lemma subseteq_guards_Await:
  "c \<subseteq>\<^sub>g\<^sub>s Await b c' e \<Longrightarrow> \<exists>c''. c=Await b c'' e \<and> (c'' \<subseteq>\<^sub>g c')"
  by (cases c) (auto)


lemma subseteq_guards_Call:
 "c \<subseteq>\<^sub>g\<^sub>s Call p \<Longrightarrow> c = Call p"
  by (cases c) (auto)

lemma subseteq_guards_DynCom:
  "c \<subseteq>\<^sub>g\<^sub>s DynCom C \<Longrightarrow> \<exists>C'. c=DynCom C' \<and> (\<forall>s. C' s \<subseteq>\<^sub>g\<^sub>s C s)"
  by (cases c) (auto)

lemma subseteq_guards_Guard:
  "c \<subseteq>\<^sub>g\<^sub>s Guard f g c'  \<Longrightarrow> 
     (c \<subseteq>\<^sub>g\<^sub>s c') \<or> (\<exists>c''. c=Guard f g c'' \<and> (c'' \<subseteq>\<^sub>g\<^sub>s c'))"
  by (cases c) (auto split: if_split_asm)

lemma subseteq_guards_Throw:
 "c \<subseteq>\<^sub>g\<^sub>s Throw \<Longrightarrow> c = Throw"
  by (cases c) (auto)

lemma subseteq_guards_Catch:
  "c \<subseteq>\<^sub>g\<^sub>s Catch c1 c2 \<Longrightarrow> \<exists>c1' c2'. c=Catch c1' c2' \<and> (c1' \<subseteq>\<^sub>g\<^sub>s c1) \<and> (c2' \<subseteq>\<^sub>g\<^sub>s c2)"
  by (cases c) (auto)

lemmas subseteq_guardsD = subseteq_guards_Skip subseteq_guards_Basic
 subseteq_guards_Spec subseteq_guards_Seq subseteq_guards_Cond subseteq_guards_While
 subseteq_guards_Call subseteq_guards_DynCom subseteq_guards_Guard
 subseteq_guards_Throw subseteq_guards_Catch subseteq_guards_Await

lemma subseteq_guards_Guard': 
  "Guard f b c \<subseteq>\<^sub>g\<^sub>s d \<Longrightarrow> \<exists>f' b' c'. d=Guard f' b' c'"
apply (cases d)
apply auto
done

lemma subseteq_guards_refl: "c \<subseteq>\<^sub>g c"
  by (induct c) auto

(* Antisymmetry and transitivity should hold as well\<dots> *)

end

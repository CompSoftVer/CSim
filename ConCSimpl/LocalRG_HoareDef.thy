(*
    Author:      David Sanan
    Maintainer:  David Sanan, sanan at ntu edu sg
    License:     LGPL
*)

(*  Title:      LocalRG_HoareDef.thy
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
theory LocalRG_HoareDef           
imports "SmallStepCon" "EmbSimpl.HoarePartialProps" "HOL-Library.Countable"
begin
section \<open>Validity  of Correctness Formulas\<close>

subsection \<open>Aux\<close>

abbreviation (input)
  set_fun :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"  ("_\<^sub>f") where
  "set_fun s \<equiv> \<lambda>v. v\<in>s"

abbreviation (input)
  fun_set :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set"  ("_\<^sub>s") where
  "fun_set f \<equiv> {\<sigma>. f \<sigma>}"


lemma tl_pair:"Suc (Suc j) < length l \<Longrightarrow>     
       l1 = tl l \<Longrightarrow>
       P (l!(Suc j)) (l!(Suc (Suc j)))=
       P  (l1!j) (l1!(Suc j))"
by (simp add: tl_zero_eq)

lemma for_all_k_sublist:
assumes a0:"Suc (Suc j)<length l" and
      a1:"(\<forall>k < j. P ((tl l)!k) ((tl l)!(Suc k)))" and
      a2:"P (l!0) (l!(Suc 0))" 
shows "(\<forall>k < Suc j.  P (l!k) (l!(Suc k)))"
proof -
  {fix k
   assume aa0:"k < Suc j"
   have "P (l!k) (l!(Suc k))"
   proof (cases k)
     case 0 thus ?thesis using a2 by auto
   next
     case (Suc k1) thus ?thesis using aa0 a0 a1 a2
       by (metis SmallStepCon.nth_tl Suc_less_SucD dual_order.strict_trans length_greater_0_conv nth_Cons_Suc zero_less_Suc)
   qed
  } thus ?thesis by auto
qed


subsection \<open>Validity for Component Programs.\<close>

type_synonym ('s,'f) tran = "('s,'f) xstate \<times> ('s,'f) xstate"
type_synonym ('s,'p,'f,'e) rgformula =  
   "(('s,'p,'f,'e) com \<times>      
    ('s set) \<times>         
    (('s,'f) tran) set \<times>
    (('s,'f) tran) set \<times>
    ('s set) \<times> 
    ('s set))" (* A *)
    
type_synonym ('s,'p,'f,'e) sextuple =  
   "('p \<times>     
    ('s set) \<times>         
    (('s,'f) tran) set \<times> 
    (('s,'f) tran) set \<times> 
    ('s set) \<times>
    ('s set))" (* A *)    

definition Sta :: "'s set \<Rightarrow> (('s,'f) tran) set \<Rightarrow> bool" where
  "Sta \<equiv> \<lambda>f g. (\<forall>x y x'. x' \<in> f \<and> x=Normal x' \<longrightarrow>  (x,y)\<in> g \<longrightarrow> (\<exists>y'. y=Normal y' \<and> y' \<in> f))"

lemma Sta_intro:"Sta a R \<Longrightarrow> Sta b R \<Longrightarrow> Sta (a \<inter> b) R"
unfolding Sta_def by fastforce

lemma Sta_assoc:"Sta (a \<inter> (b \<inter> c)) R = Sta ((a\<inter>b)\<inter>c) R"
unfolding Sta_def by fastforce

lemma Sta_comm:"Sta (a \<inter> b) R = Sta (b \<inter> a) R" 
unfolding Sta_def by fastforce

lemma Sta_add:"Sta (a \<inter> b) R \<Longrightarrow> Sta (a \<inter> c) R \<Longrightarrow>
       Sta (a \<inter> b \<inter> c) R"
unfolding Sta_def by fastforce

lemma Sta_tran:"Sta a R \<Longrightarrow> a = b \<Longrightarrow> Sta b R"
by auto

definition Norm:: "(('s,'f) tran) set \<Rightarrow> bool" where
  "Norm \<equiv> \<lambda>g. (\<forall>x y. (x, y) \<in> g \<longrightarrow> (\<exists>x' y'. x=Normal x' \<and> y=Normal y'))"

definition env_tran::
    "('p \<Rightarrow> ('s, 'p, 'f,'e) LanguageCon.com option)
     \<Rightarrow> ('s set)
        \<Rightarrow> (('s, 'p, 'f,'e) LanguageCon.com \<times> ('s, 'f) xstate) list
           \<Rightarrow> ('s,'f) tran set \<Rightarrow> bool"
where
"env_tran \<Gamma> q l rely \<equiv> snd(l!0) \<in> Normal ` q \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                  
                   (snd(l!i), snd(l!(Suc i))) \<in> rely)
"

definition env_tran_right::
    "('p \<Rightarrow> ('s, 'p, 'f,'e) LanguageCon.com option)     
        \<Rightarrow> (('s, 'p, 'f,'e) LanguageCon.com \<times> ('s, 'f) xstate) list
           \<Rightarrow> ('s,'f) tran set \<Rightarrow> bool"
where
"env_tran_right \<Gamma> l rely \<equiv> 
   (\<forall>i. Suc i<length l \<longrightarrow> 
        \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                  
        (snd(l!i), snd(l!(Suc i))) \<in> rely)
"

lemma env_tran_tail:"env_tran_right \<Gamma> (x#l) R \<Longrightarrow> env_tran_right \<Gamma> l R"
unfolding env_tran_right_def
by fastforce

lemma env_tran_subr:
assumes a0:"env_tran_right \<Gamma> (l1@l2) R"
shows "env_tran_right \<Gamma> l1 R"
unfolding env_tran_right_def
proof -
  {fix i
  assume a1:"Suc i< length l1"
  assume a2:"\<Gamma>\<turnstile>\<^sub>c l1 ! i \<rightarrow>\<^sub>e l1 ! Suc i"
  then have "Suc i < length (l1@l2)" using a1 by fastforce
  also then have "\<Gamma>\<turnstile>\<^sub>c (l1@l2) ! i \<rightarrow>\<^sub>e (l1@l2) ! Suc i" 
  proof -
    show ?thesis
      by (simp add: Suc_lessD a1 a2 nth_append)
  qed
  ultimately have f1:"(snd ((l1@l2)! i), snd ((l1@l2) ! Suc i)) \<in> R"
  using a0 unfolding env_tran_right_def by auto
  then have "(snd (l1! i), snd (l1 ! Suc i)) \<in>  R"
  using a1
proof -
  have "\<forall>ps psa n. if n < length ps then (ps @ psa) ! n = (ps ! n::('b, 'a, 'c,'d) LanguageCon.com \<times> ('b, 'c) xstate) 
                   else (ps @ psa) ! n = psa ! (n - length ps)"
    by (meson nth_append)
  then show ?thesis
    using f1 \<open>Suc i < length l1\<close> by force
qed 
  } then show 
   "\<forall>i. Suc i < length l1 \<longrightarrow>
        \<Gamma>\<turnstile>\<^sub>c l1 ! i \<rightarrow>\<^sub>e l1 ! Suc i \<longrightarrow>
        (snd (l1 ! i), snd (l1 ! Suc i)) \<in> R"
   by blast
qed

definition Satis where "Satis \<equiv> True"

definition sep_conj where "sep_conj \<equiv> True"

lemma env_tran_subl:"env_tran_right \<Gamma> (l1@l2) R \<Longrightarrow> env_tran_right \<Gamma> l2 R"
proof (induct "l1")
  case Nil thus ?case by auto
next
  case (Cons a l1) thus ?case by (fastforce intro:append_Cons env_tran_tail )
qed

lemma env_tran_R_R':"env_tran_right \<Gamma> l R \<Longrightarrow>  
                     (R  \<subseteq> R') \<Longrightarrow>
                     env_tran_right \<Gamma> l R'"
unfolding env_tran_right_def Satis_def sep_conj_def
apply clarify
apply (erule allE)
apply auto
done


lemma env_tran_normal:
assumes a0:"env_tran_right \<Gamma> l rely \<and> Sta q rely \<and>  snd(l!i) = Normal s1 \<and> s1\<in>q" and
        a1:"Suc i < length l \<and>  \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))"
shows "\<exists>s1 s2. snd(l!i) = Normal s1 \<and> snd(l!(Suc i)) = Normal s2 \<and> s2\<in>q"
using a0 a1 unfolding env_tran_right_def Sta_def by fastforce

lemma no_env_tran_not_normal:
assumes a0:"env_tran_right \<Gamma> l rely \<and> Sta q rely \<and>  snd(l!i) = Normal s1 \<and> s1\<in>q" and
        a1:"Suc i < length l \<and>  \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))" and
        a2:"(\<forall>s1. \<not> (snd(l!i) = Normal s1)) \<or> (\<forall>s2. \<not> (snd (l!Suc i) = Normal s2))"
shows "P"
using a0 a1 a2 unfolding env_tran_right_def Sta_def by fastforce 
 
definition assum :: 
  "('s set \<times> ('s,'f) tran set) \<Rightarrow> (('s,'p,'f,'e) confs) set" where
  "assum \<equiv> \<lambda>(pre, rely). 
             {c. snd((snd c)!0) \<in> Normal ` pre \<and> 
                 (\<forall>i. Suc i<length (snd c) \<longrightarrow> 
                 (fst c)\<turnstile>\<^sub>c((snd c)!i)  \<rightarrow>\<^sub>e ((snd c)!(Suc i)) \<longrightarrow>                  
                   (snd((snd c)!i), snd((snd c)!(Suc i))) \<in>  rely)}"

definition assum1 :: 
  "('s set \<times> ('s,'f) tran set) \<Rightarrow>
   'f set \<Rightarrow>
     (('s,'p,'f,'e) confs) set" where
  "assum1 \<equiv> \<lambda>(pre, rely) F. 
             {(\<Gamma>,comp). snd(comp!0) \<in> Normal ` pre \<and> 
                 (\<forall>i. Suc i<length comp \<longrightarrow> 
                  \<Gamma>\<turnstile>\<^sub>c(comp!i)  \<rightarrow>\<^sub>e (comp!(Suc i)) \<longrightarrow>                  
                   (snd(comp!i), snd(comp!(Suc i))) \<in>  rely)}"


lemma assum_R_R': 
  "(\<Gamma>, l) \<in> assum(p, R) \<Longrightarrow>
    snd(l!0) \<in> Normal `  p' \<Longrightarrow>
    R \<subseteq> R'  \<Longrightarrow> 
   (\<Gamma>, l) \<in> assum(p', R')"
proof -
assume a0:"(\<Gamma>, l) \<in> assum(p, R)" and
       a1:"snd(l!0) \<in> Normal `  p'" and
       a2: " R \<subseteq> R'"
  then have "env_tran_right \<Gamma> l R" 
    unfolding assum_def using env_tran_right_def
    by force
  then have "env_tran_right \<Gamma> l R'" 
    using  a2 env_tran_R_R' by blast
  thus ?thesis using a1 unfolding assum_def unfolding env_tran_right_def
    by fastforce
qed


lemma same_prog_p:
  "(\<Gamma>,(P,s)#(P,t)#l)\<in>cptn \<Longrightarrow>
   (\<Gamma>,(P,s)#(P,t)#l) \<in> assum (p,R) \<Longrightarrow>
   Sta p R  \<Longrightarrow>
   \<exists>t1. t=Normal t1 \<and> t1 \<in> p
  " 
proof -
assume a0: "(\<Gamma>,(P,s)#(P,t)#l)\<in>cptn" and
         a1: "(\<Gamma>,(P,s)#(P,t)#l) \<in> assum (p,R)" and
         a2: "Sta p R"
  then have "Suc 0 < length ((P,s)#(P,t)#l)" 
    by fastforce
  then have "\<Gamma>\<turnstile>\<^sub>c(((P,s)#(P,t)#l)!0)  \<rightarrow>\<^sub>c\<^sub>e (((P,s)#(P,t)#l)!(Suc 0))" 
    using a0 cptn_stepc_rtran by fastforce 
  then have step_ce:"\<Gamma>\<turnstile>\<^sub>c(((P,s)#(P,t)#l)!0)  \<rightarrow>\<^sub>e (((P,s)#(P,t)#l)!(Suc 0)) \<or>
             \<Gamma>\<turnstile>\<^sub>c(((P,s)#(P,t)#l)!0)  \<rightarrow> (((P,s)#(P,t)#l)!(Suc 0))"
    using step_ce_elim_cases by blast  
  then obtain s1 where s:"s=Normal s1 \<and> s1 \<in> p" 
    using a1 unfolding assum_def
    by fastforce
  have "\<exists>t1. t=Normal t1 \<and> t1 \<in> p "
  using step_ce
  proof
    {assume step_e:"\<Gamma>\<turnstile>\<^sub>c ((P, s) # (P, t) # l) ! 0 \<rightarrow>\<^sub>e
          ((P, s) # (P, t) # l) ! Suc 0"
     have ?thesis 
     using a2 a1 s unfolding Sta_def assum_def 
     proof -
       have "(Suc 0 < length ((P, s) # (P, t) # l))"
         by fastforce
       then have assm:"(s, t) \<in> R"
         using s a1 step_e
         unfolding assum_def  by fastforce
       then obtain t1 s2 where s_t:"s= Normal s2 \<and> t = Normal t1" 
         using a2 s unfolding Sta_def by fastforce 
       then have R:"(s,t)\<in>R" 
         using assm  unfolding Satis_def by fastforce
       then have "s2=s1" using s s_t by fastforce
       then have "t1\<in>p" 
         using a2 s s_t R unfolding Sta_def Norm_def by blast
       thus ?thesis using s_t by blast
     qed thus ?thesis by auto
    } 
    next
    { 
      assume step:"\<Gamma>\<turnstile>\<^sub>c ((P, s) # (P, t) # l) ! 0 \<rightarrow>
          ((P, s) # (P, t) # l) ! Suc 0"
      then have "P\<noteq>P \<or> s=t"
      proof -
        have "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow> (P, t)"
          using local.step by force
        then show ?thesis
          using step_change_p_or_eq_s by blast
      qed
      then show ?thesis using s by fastforce
    }
  qed thus  ?thesis by auto
qed

lemma tl_of_assum_in_assum:
  "(\<Gamma>,(P,s)#(P,t)#l)\<in>cptn \<Longrightarrow>
   (\<Gamma>,(P,s)#(P,t)#l) \<in> assum (p,R) \<Longrightarrow>
   Sta p R  \<Longrightarrow>
   (\<Gamma>,(P,t)#l) \<in> assum (p,R)
  " 
proof -
  assume a0: "(\<Gamma>,(P,s)#(P,t)#l)\<in>cptn" and
         a1: "(\<Gamma>,(P,s)#(P,t)#l) \<in> assum (p,R)" and
         a2: "Sta p R "
  
  then obtain t1 where t1:"t=Normal t1 \<and> t1 \<in>p" 
   using same_prog_p by blast
  then have "env_tran_right \<Gamma> ((P,s)#(P,t)#l) R"
    using env_tran_right_def a1 unfolding assum_def
    by force
  then have "env_tran_right \<Gamma> ((P,t)#l) R"
    using env_tran_tail by auto
  thus ?thesis using t1 unfolding assum_def env_tran_right_def by auto
qed

lemma tl_of_assum_in_assum1:
  "(\<Gamma>,(P,s)#(Q,t)#l)\<in>cptn \<Longrightarrow>
   (\<Gamma>,(P,s)#(Q,t)#l) \<in> assum (p,R) \<Longrightarrow>
   t \<in> Normal ` q \<Longrightarrow>
   (\<Gamma>,(Q,t)#l) \<in> assum (q,R) 
  " 
proof -
  assume a0: "(\<Gamma>,(P,s)#(Q,t)#l)\<in>cptn" and
         a1: "(\<Gamma>,(P,s)#(Q,t)#l) \<in> assum (p,R)" and
         a2: "t \<in> Normal ` q"  
  then have "env_tran_right \<Gamma> ((P,s)#(Q,t)#l) R"
    using env_tran_right_def a1 unfolding assum_def
    by force
  then have "env_tran_right \<Gamma> ((Q,t)#l) R"
    using env_tran_tail by auto
  thus ?thesis using a2 unfolding assum_def env_tran_right_def by auto
qed
            
lemma sub_assum:
  assumes a0: "(\<Gamma>,(x#l0)@l1) \<in> assum (p,R)"
  shows "(\<Gamma>,x#l0) \<in> assum (p,R)"    
proof -
  {have p0:"snd x \<in> Normal ` p" 
    using a0 unfolding assum_def by force
  then have "env_tran_right \<Gamma> ((x#l0)@l1) R"
    using a0 unfolding assum_def 
    by (auto simp add: env_tran_right_def)
  then have env:"env_tran_right \<Gamma> (x#l0) R" 
    using env_tran_subr by blast 
  also have "snd ((x#l0)!0)  \<in> Normal ` p" 
    using p0 by fastforce
  ultimately have "snd ((x#l0)!0)  \<in> Normal ` p \<and> 
                  (\<forall>i. Suc i<length (x#l0) \<longrightarrow> 
                       \<Gamma>\<turnstile>\<^sub>c((x#l0)!i)  \<rightarrow>\<^sub>e ((x#l0)!(Suc i)) \<longrightarrow>                  
                       (snd((x#l0)!i), snd((x#l0)!(Suc i))) \<in> R)"
   unfolding env_tran_right_def by auto
  }    
  then show ?thesis  unfolding assum_def by auto
qed      

lemma sub_assum_r:
  assumes a0: "(\<Gamma>,l0@x1#l1) \<in> assum (p,R)" and
          a1: "(snd x1) \<in> Normal ` q"
  shows "(\<Gamma>,x1#l1) \<in> assum (q,R)"
proof -
  have "env_tran_right  \<Gamma> (l0@x1#l1) R"
    using a0 unfolding assum_def env_tran_right_def
    by fastforce
  then have "env_tran_right \<Gamma> (x1#l1) R"
    using env_tran_subl by auto
  thus ?thesis using a1 unfolding assum_def env_tran_right_def by fastforce
qed

definition comm :: 
  "(('s,'f) tran) set \<times> 
   ('s set \<times> 's set) \<Rightarrow>
   'f set \<Rightarrow> 
     (('s,'p,'f,'e) confs) set" where
  "comm \<equiv> \<lambda>(guar, (q,a)) F. 
            {c. snd (last (snd c)) \<notin> Fault ` F  \<longrightarrow> 
                (\<forall>i. 
                 Suc i<length (snd c) \<longrightarrow> 
                 (fst c)\<turnstile>\<^sub>c((snd c)!i)  \<rightarrow> ((snd c)!(Suc i)) \<longrightarrow>                                        
                   (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> guar) \<and> 
                 (final (last (snd c))  \<longrightarrow>                   
                    ((fst (last (snd c)) = Skip \<and> 
                      snd (last (snd c)) \<in> Normal ` q)) \<or>
                    (fst (last (snd c)) = Throw \<and> 
                      snd (last (snd c)) \<in> Normal ` a))}"

definition comm1 :: 
  "(('s,'f) tran) set \<times> 
   ('s set \<times> 's set) \<Rightarrow>
   'f set \<Rightarrow> 
     (('s,'p,'f,'e) confs) set" where
  "comm1 \<equiv> \<lambda>(guar, (q,a)) F. 
            {(\<Gamma>,comp). snd (last comp) \<notin> Fault ` F  \<longrightarrow> 
                (\<forall>i. 
                 Suc i<length comp \<longrightarrow> 
                 \<Gamma>\<turnstile>\<^sub>c(comp!i)  \<rightarrow> (comp!(Suc i)) \<longrightarrow>                                        
                   (snd(comp!i), snd(comp!(Suc i))) \<in> guar) \<and> 
                 (final (last comp)  \<longrightarrow>                   
                    ((fst (last comp) = Skip \<and> 
                      snd (last comp) \<in> Normal ` q)) \<or>
                    (fst (last comp) = Throw \<and> 
                      snd (last comp) \<in> Normal ` a))}"

lemma comm_dest:
"(\<Gamma>, l)\<in> comm (G,(q,a)) F \<Longrightarrow>
 snd (last l) \<notin> Fault ` F \<Longrightarrow>
 (\<forall>i. Suc i<length l \<longrightarrow>
   \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow> 
    (snd(l!i), snd(l!(Suc i))) \<in>  G)"
unfolding comm_def
apply clarify
apply (drule mp)
apply fastforce
apply (erule conjE)
apply (erule allE)
by auto

lemma comm_dest1:
"(\<Gamma>, l)\<in> comm (G,(q,a)) F \<Longrightarrow>
 snd (last l) \<notin> Fault ` F \<Longrightarrow>
 Suc i<length l \<Longrightarrow>
 \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<Longrightarrow>
(snd(l!i), snd(l!(Suc i))) \<in> G"
unfolding comm_def
apply clarify
apply (drule mp)
apply fastforce
apply (erule conjE)
apply (erule allE)
by auto

lemma comm_dest2:
  assumes a0: "(\<Gamma>, l)\<in> comm (G,(q,a)) F" and
          a1: "final (last l)" and
          a2: "snd (last l) \<notin> Fault ` F" 
  shows  " ((fst (last l) = Skip \<and> 
            snd (last l) \<in> Normal ` q)) \<or>
            (fst (last l) = Throw \<and> 
            snd (last l) \<in> Normal ` a)"
proof -
  show ?thesis using a0 a1 a2 unfolding comm_def by auto
qed

lemma comm_des3:
  assumes a0: "(\<Gamma>, l)\<in> comm (G,(q,a)) F" and
          a1: "snd (last l) \<notin> Fault ` F"
 shows "final (last l) \<longrightarrow> ((fst (last l) = Skip \<and> 
            snd (last l) \<in> Normal ` q)) \<or>
            (fst (last l) = Throw \<and> 
            snd (last l) \<in> Normal ` a)"
using a0 a1 unfolding comm_def by auto

lemma commI:
  assumes a0:"snd (last l) \<notin> Fault ` F \<Longrightarrow>
             (\<forall>i. 
                 Suc i<length l \<longrightarrow> 
                 \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow>                                               
                   (snd(l!i), snd(l!(Suc i))) \<in> G) \<and> 
                 (final (last l)  \<longrightarrow>                   
                    ((fst (last l) = Skip \<and> 
                      snd (last l) \<in> Normal ` q)) \<or>
                    (fst (last l) = Throw \<and> 
                      snd (last l) \<in> Normal ` a))"
shows "(\<Gamma>,l)\<in>comm (G, (q,a)) F"
using a0  unfolding comm_def
apply clarify
by simp

lemma comm_conseq:
  "(\<Gamma>,l) \<in> comm(G', (q',a')) F \<Longrightarrow>
       G' \<subseteq> G \<and>
       q' \<subseteq> q \<and>
       a' \<subseteq> a \<Longrightarrow>
      (\<Gamma>,l) \<in> comm (G,(q,a)) F"
proof -
  assume a0:"(\<Gamma>,l) \<in> comm(G', (q',a')) F" and
         a1:" G' \<subseteq> G  \<and>
        q' \<subseteq> q \<and>
        a' \<subseteq> a"
  {
    assume a:"snd (last l) \<notin> Fault ` F "
    have l:"(\<forall>i. 
           Suc i<length l \<longrightarrow> 
           \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow>                                          
             (snd(l!i), snd(l!(Suc i))) \<in> G)"
    proof -
      {fix i ns ns'
      assume a00:"Suc i<length l" and
             a11:"\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i))"             
      have "(snd(l!i), snd(l!(Suc i))) \<in>  G" 
      proof -
        have "(snd(l!i), snd(l!(Suc i))) \<in>  G'"
        using comm_dest1 [OF a0 a a00 a11]  by auto
        thus ?thesis using a1 unfolding Satis_def sep_conj_def by fastforce
      qed
      } thus ?thesis by auto
    qed  
    have "(final (last l)  \<longrightarrow>                   
                    ((fst (last l) = Skip \<and> 
                      snd (last l) \<in> Normal ` q)) \<or>
                    (fst (last l) = Throw \<and> 
                      snd (last l) \<in> Normal ` a))"
    proof -
      {assume a33:"final (last l)"
      then have "((fst (last l) = Skip \<and> 
                      snd (last l) \<in> Normal ` q')) \<or>
                    (fst (last l) = Throw \<and> 
                      snd (last l) \<in> Normal ` a')"
      using comm_dest2[OF a0 a33 a] by auto
      then have "((fst (last l) = Skip \<and> 
                      snd (last l) \<in> Normal ` q)) \<or>
                    (fst (last l) = Throw \<and> 
                      snd (last l) \<in> Normal ` a)"
      using a1 by fastforce
     } thus ?thesis by auto
    qed
    note res1 = conjI[OF l this] 
  } thus ?thesis unfolding comm_def by simp
qed   

lemma  no_comp_tran_no_final_comm:
  assumes a0:"\<forall>i<length l. \<not> final (l!i)" and
          a1:"\<forall>i<length l. fst (l!i) = C" and a2:"length l>0"
        shows "(\<Gamma>,l)\<in>comm(G, (q,a)) F"
proof-
  have n_comp:"\<forall>i. Suc i < length l \<longrightarrow> \<not> (\<Gamma>\<turnstile>\<^sub>c (l!i) \<rightarrow> (l!Suc i))" using a1
    by (metis Suc_lessD mod_env_not_component prod.collapse)
  {assume a00:"snd (last l) \<notin> Fault ` F" 
    {fix i
      assume "Suc i< length(l)" and 
             "\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i))"  
      then have False using n_comp by auto
    }
    moreover {
      assume "final (last l)"
      then have False using a0 a2
        using last_conv_nth by force
      }
      ultimately have ?thesis unfolding comm_def using a00 by auto
  } thus ?thesis unfolding comm_def by auto   
qed

definition com_validity :: 
  "('s,'p,'f,'e) body \<Rightarrow>  'f set \<Rightarrow> ('s,'p,'f,'e) com \<Rightarrow> 
    's set \<Rightarrow> (('s,'f) tran) set \<Rightarrow>  (('s,'f) tran) set \<Rightarrow>  
    's set \<Rightarrow>  's set \<Rightarrow>  bool" 
    ("_ \<Turnstile>\<^bsub>'/_\<^esub>/ _ sat [_,_, _, _,_]" [61,60,0,0,0,0,0,0] 45) where
  "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a] \<equiv> 
   \<forall>s. cp \<Gamma> Pr s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"

definition com_cvalidity::
 "('s,'p,'f,'e) body \<Rightarrow>
    ('s,'p,'f,'e) sextuple set \<Rightarrow>
    'f set \<Rightarrow>
    ('s,'p,'f,'e) com \<Rightarrow> 
    's set \<Rightarrow>          
    (('s,'f) tran) set \<Rightarrow> 
    (('s,'f) tran) set \<Rightarrow>  
    's set \<Rightarrow> 
    's set \<Rightarrow>
      bool" 
    ("_,_ \<Turnstile>\<^bsub>'/_\<^esub>/ _ sat [_,_, _, _,_]" [61,60,0,0,0,0,0,0] 45) where
  "\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a] \<equiv> 
   (\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]) \<longrightarrow> 
     \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a]"

definition com_validityn :: 
  "('s,'p,'f,'e) body \<Rightarrow> nat \<Rightarrow> 'f set  \<Rightarrow> ('s,'p,'f,'e) com \<Rightarrow> 
    's set \<Rightarrow> (('s,'f) tran) set \<Rightarrow>  (('s,'f) tran) set \<Rightarrow>  
    's set \<Rightarrow>  's set \<Rightarrow>  bool" 
    ("_ \<Turnstile>_\<^bsub>'/_\<^esub>/ _ sat [_,_, _, _,_]" [61,0,60,0,0,0,0,0,0] 45) where
  "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a] \<equiv> 
   \<forall>s. cpn n \<Gamma> Pr s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"

definition com_cvalidityn::
 "('s,'p,'f,'e) body \<Rightarrow>
    ('s,'p,'f,'e) sextuple set \<Rightarrow> nat \<Rightarrow>
    'f set \<Rightarrow>
    ('s,'p,'f,'e) com \<Rightarrow> 
    's set \<Rightarrow>          
    (('s,'f) tran) set \<Rightarrow> 
    (('s,'f) tran) set \<Rightarrow>  
    's set \<Rightarrow> 
    's set \<Rightarrow>
      bool" 
    ("_,_ \<Turnstile>_\<^bsub>'/_\<^esub>/ _ sat [_,_, _, _,_]" [61,60,0,0,0,0,0,0,0] 45) where
  "\<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a] \<equiv> 
   (\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]) \<longrightarrow> 
     \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a]"


lemma com_valid_iff_nvalid:"(\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a]) = (\<forall>n. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a])"
  apply (simp only: com_validity_def com_validityn_def cp_def cpn_def cptn_eq_cptn_mod_nest)
  by fast

lemma com_cnvalid_to_cvalid: "(\<forall>n. (\<Gamma>,\<Theta>\<Turnstile>n\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a])) \<Longrightarrow> (\<Gamma>,\<Theta>\<Turnstile>\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a])"
  apply (unfold com_cvalidityn_def com_cvalidity_def com_valid_iff_nvalid [THEN eq_reflection])
  by fast


lemma etran_in_comm:
  "(\<Gamma>,(P, t) # xs) \<in> comm(G, (q,a)) F  \<Longrightarrow> 
    \<not> (\<Gamma>\<turnstile>\<^sub>c((P,s))  \<rightarrow> ((P,t))) \<Longrightarrow>
    (\<Gamma>,(P, s) # (P, t) # xs) \<in> cptn \<Longrightarrow>    
   (\<Gamma>,(P, s) # (P, t) # xs) \<in> comm(G, (q,a)) F" 
proof -
  assume a1:"(\<Gamma>,(P, t) # xs) \<in> comm(G, (q,a)) F" and
         a2:"\<not> \<Gamma>\<turnstile>\<^sub>c((P,s))  \<rightarrow> ((P,t))" and
         a3:"(\<Gamma>,(P, s) # (P, t) # xs) \<in> cptn"
  show ?thesis using comm_def a1 a2 a3
  proof -
     {
     let ?l1 = "(P, t) # xs"
     let ?l = "(P, s) # ?l1"
     assume a00:"snd (last ?l) \<notin> Fault ` F"
     have concl:"(\<forall>i ns ns'. Suc i<length ?l \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c(?l!i)  \<rightarrow> (?l!(Suc i)) \<longrightarrow>                          
                 (snd(?l!i), snd(?l!(Suc i))) \<in>  G)"
     proof -
       {fix i ns ns'
        assume a11:"Suc i < length  ?l" and
               a12:"\<Gamma>\<turnstile>\<^sub>c (?l ! i) \<rightarrow> ( ?l ! Suc i)"               
        have p1:"(\<forall>i ns ns'. Suc i<length ?l1 \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c(?l1!i)  \<rightarrow> (?l1!(Suc i)) \<longrightarrow>                             
               (snd(?l1!i), snd(?l1!(Suc i))) \<in>  G)"
        using a1 a3 a00 unfolding comm_def by auto
        have "(snd (?l ! i), snd (?l ! Suc i)) \<in>  G"         
        proof (cases i)
          case 0 
          have  "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow> (P, t)" using a12 0 by auto
          thus ?thesis using a2 by auto             
        next
          case (Suc n) thus ?thesis
          proof -
            have f1: "\<Gamma>\<turnstile>\<^sub>c ((P, t) # xs) ! n \<rightarrow> ((P, t) # xs) ! Suc n"
              using Suc a12 by fastforce
            have f2: "Suc n < length ((P, t) # xs)"
              using Suc a11 by fastforce                       
            have "snd (last ((P, t) # xs)) \<notin> Fault ` F"
                by (metis (no_types) a00 last.simps list.distinct(1))
            hence "(snd (((P, t) # xs) ! n), snd (((P, t) # xs) ! Suc n)) \<in> G"
              using f2 f1 a1 comm_dest1  by blast            
            thus ?thesis
              by (simp add: Suc)
          qed  
        qed
       } thus ?thesis by auto
     qed
     have concr:"(final (last ?l)  \<longrightarrow>                   
                    ((fst (last ?l) = Skip \<and> 
                      snd (last ?l) \<in> Normal ` q)) \<or>
                    (fst (last ?l) = Throw \<and> 
                      snd (last ?l) \<in> Normal ` a))"
     using a1 a00 unfolding comm_def by auto
     note res1=conjI[OF concl concr] }   
     thus ?thesis unfolding comm_def by auto qed
qed

lemma ctran_in_comm:   
  " (Normal s,Normal s) \<in> G  \<Longrightarrow>
   (\<Gamma>,(Q, Normal s) # xs) \<in> comm(G, (q,a)) F  \<Longrightarrow>        
   (\<Gamma>,(P, Normal s) # (Q, Normal s) # xs) \<in> comm(G, (q,a)) F"
proof -
  assume a1:"(Normal s,Normal s) \<in> G" and
         a2:"(\<Gamma>,(Q, Normal s) # xs) \<in> comm(G, (q,a)) F"          
  show ?thesis using comm_def a1 a2
  proof -
     {
     let ?l1 = "(Q, Normal s) # xs"
     let ?l = "(P, Normal s) # ?l1"
      assume a00:"snd (last ?l) \<notin> Fault ` F"
     have concl:"(\<forall>i. Suc i<length ?l \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c(?l!i)  \<rightarrow> (?l!(Suc i)) \<longrightarrow>                                              
                 (snd(?l!i), snd(?l!(Suc i))) \<in>  G)"
     proof -
       {fix i ns ns'
        assume a11:"Suc i < length  ?l" and
               a12:"\<Gamma>\<turnstile>\<^sub>c (?l ! i) \<rightarrow> ( ?l ! Suc i)" 
        have p1:"(\<forall>i. Suc i<length ?l1 \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c(?l1!i)  \<rightarrow> (?l1!(Suc i)) \<longrightarrow>                              
               (snd(?l1!i), snd(?l1!(Suc i))) \<in>  G)"
        using a2 a00 unfolding comm_def by auto
        have "(snd (?l ! i), snd (?l ! Suc i)) \<in> G"   
        proof (cases i)
          case 0     
          then have "snd (((P, Normal s) # (Q, Normal s) # xs) ! i) = Normal s \<and> 
                     snd (((P, Normal s) # (Q, Normal s) # xs) ! (Suc i)) = Normal s"                
            by fastforce
          also have "(Normal s, Normal s) \<in> G"
             using Satis_def a1 by blast
          ultimately show  ?thesis using a1 Satis_def by auto            
        next
          case (Suc n) thus ?thesis using p1 a2  a11 a12 
          proof -
            have f1: "\<Gamma>\<turnstile>\<^sub>c ((Q, Normal s) # xs) ! n \<rightarrow> ((Q, Normal s) # xs) ! Suc n"
              using Suc a12 by fastforce
            have f2: "Suc n < length ((Q, Normal s) # xs)"
              using Suc a11 by fastforce
            thus ?thesis using Suc f1 nth_Cons_Suc p1 by auto 
          qed  
        qed
       } thus ?thesis by auto
     qed
     have concr:"(final (last ?l)  \<longrightarrow> 
                  snd (last ?l) \<notin> Fault ` F  \<longrightarrow>
                    ((fst (last ?l) = Skip \<and> 
                      snd (last ?l) \<in> Normal ` q)) \<or>
                    (fst (last ?l) = Throw \<and> 
                      snd (last ?l) \<in> Normal ` a))"
     using a2 unfolding comm_def by auto
     note res=conjI[OF concl concr]}
     thus ?thesis unfolding comm_def by auto qed
qed

lemma not_final_in_comm:
 "(\<Gamma>,(Q, Normal s) # xs) \<in> comm(G, (q,a)) F \<Longrightarrow>
  \<not> final (last ((Q, Normal s) # xs)) \<Longrightarrow>
  (\<Gamma>,(Q, Normal s) # xs) \<in> comm(G, (q',a')) F"
unfolding comm_def by force

lemma comm_union:
 assumes 
   a0: "(\<Gamma>,xs) \<in> comm(G, (q,a)) F" and
   a1: "(\<Gamma>,ys) \<in> comm(G, (q',a')) F" and
   a2: "xs\<noteq>[] \<and> ys\<noteq>[]" and
   a3: "( snd (last xs),snd (ys!0)) \<in> G" and
   a4: "(\<Gamma>,xs@ys) \<in> cptn"
 shows "(\<Gamma>,xs@ys) \<in> comm(G, (q',a')) F" 
proof -
{
  let ?l="xs@ys" 
  assume a00:"snd (last (xs@ys)) \<notin> Fault ` F"
  have last_ys:"last (xs@ys) = last ys" using a2 by fastforce
  have concl:"(\<forall>i. Suc i<length ?l \<longrightarrow> 
             \<Gamma>\<turnstile>\<^sub>c(?l!i)  \<rightarrow> (?l!(Suc i)) \<longrightarrow>                                            
               (snd(?l!i), snd(?l!(Suc i))) \<in> G)"
   proof -
     {fix i ns ns'
      assume a11:"Suc i < length  ?l" and
             a12:"\<Gamma>\<turnstile>\<^sub>c (?l ! i) \<rightarrow> ( ?l ! Suc i)" 
      have all_ys:"\<forall>i\<ge>length xs. (xs@ys)!i = ys!(i-(length xs))"
          by (simp add: nth_append)   
      have all_xs:"\<forall>i<length xs. (xs@ys)!i = xs!i"
            by (simp add: nth_append)
      have "(snd(?l!i), snd(?l!(Suc i))) \<in>  G"
      proof (cases "Suc i>length xs")
        case True                                 
        have "Suc (i - (length xs)) < length ys" using a11 True by fastforce
        moreover have "\<Gamma>\<turnstile>\<^sub>c (ys ! (i-(length xs))) \<rightarrow> ( ys ! ((Suc i)-(length xs)))" 
          using a12 all_ys True by fastforce          
        moreover have "snd (last ys) \<notin> Fault ` F" using last_ys a00 by fastforce   
        ultimately have "(snd(ys!(i-(length xs))), snd(ys!Suc (i-(length xs)))) \<in> G" 
        using a1 comm_dest1[of \<Gamma> ys G q' a' F "i-length xs"] True Suc_diff_le by fastforce 
        thus ?thesis using True all_ys Suc_diff_le by fastforce
      next
        case False note F1=this  thus ?thesis 
        proof (cases "Suc i < length xs")
          case True              
          then have "snd ((xs@ys)!(length xs -1)) \<notin> Fault ` F"
            using a00 a2 a4 
             by (simp add: last_not_F )         
          then have "snd (last xs) \<notin> Fault ` F" using all_xs a2 by (simp add: last_conv_nth )          
          moreover have "\<Gamma>\<turnstile>\<^sub>c (xs ! i) \<rightarrow> ( xs ! Suc i)" 
            using True all_xs a12 by fastforce          
          ultimately have"(snd(xs!i), snd(xs!(Suc i))) \<in> G"
            using a0 comm_dest1[of \<Gamma> xs G q a F i] True by fastforce
          thus ?thesis using True all_xs by fastforce
        next
          case False
          then have suc_i:"Suc i = length xs" using F1 by fastforce
          then have i:"i=length xs -1" using a2 by fastforce          
          then show ?thesis using a3 
            by (simp add: a2 all_xs all_ys  last_conv_nth ) 
        qed
      qed
     } thus ?thesis by auto          
   qed
   have concr:"(final (last ?l)  \<longrightarrow>                 
                  ((fst (last ?l) = Skip \<and> 
                    snd (last ?l) \<in> Normal ` q')) \<or>
                  (fst (last ?l) = Throw \<and> 
                    snd (last ?l) \<in> Normal ` a'))"
   using a1 last_ys a00 a2 comm_des3 by fastforce
   note res=conjI[OF concl concr]}
   thus ?thesis unfolding comm_def by auto 
qed



lemma cpn_rule1:"(\<forall>s. cpn n \<Gamma> P s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F) \<Longrightarrow>
      (\<forall>s l. (\<Gamma>,l)\<in>cpn n \<Gamma> P s \<and> (\<Gamma>,l)\<in> assum (p, R) \<longrightarrow> (\<Gamma>,l) \<in> comm(G, (q,a)) F)"
proof-
  assume a0:"\<forall>s. cpn n \<Gamma> P s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
  {fix s l    
    assume a00:"(\<Gamma>,l)\<in>cpn n \<Gamma> P s \<and> (\<Gamma>,l)\<in> assum (p, R)"    
    then have "cpn n \<Gamma> P s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F" using a0 by auto    
    then have "(\<Gamma>,l) \<in> comm(G, (q,a)) F" using a00 unfolding cpn_def assum_def comm_def
      by blast
    } then show ?thesis by auto
  qed

lemma cpn_rule2:"(\<forall>s l. (\<Gamma>,l)\<in>cpn n \<Gamma> P s \<and> (\<Gamma>,l)\<in> assum (p, R) \<longrightarrow> (\<Gamma>,l) \<in> comm(G, (q,a)) F) \<Longrightarrow>
                (\<forall>s. cpn n \<Gamma> P s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F)"
proof-
  assume a0:"\<forall>s l. (\<Gamma>,l)\<in>cpn n \<Gamma> P s \<and> (\<Gamma>,l)\<in> assum (p, R) \<longrightarrow> (\<Gamma>,l) \<in> comm(G, (q,a)) F"
  {fix s l
     assume a00:"(\<Gamma>,l)\<in> cpn n \<Gamma> P s \<and> (\<Gamma>,l)\<in>assum(p, R)"        
    then have "(\<Gamma>,l) \<in> comm(G, (q,a)) F" using a0 unfolding cpn_def assum_def comm_def
      by blast
   } then show ?thesis  unfolding cpn_def by fastforce
 qed

lemma cpn_rule:"(\<forall>s l. (\<Gamma>,l)\<in>cpn n \<Gamma> P s \<and> (\<Gamma>,l)\<in> assum (p, R) \<longrightarrow> (\<Gamma>,l) \<in> comm(G, (q,a)) F) =
                (\<forall>s. cpn n \<Gamma> P s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F)"
  using cpn_rule1 cpn_rule2
  by metis

lemma split_list_i:"i<length l \<Longrightarrow>
                    \<exists>l1 l2. l = l1@(l!i#l2)"
proof(induct l arbitrary: i)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case
    using id_take_nth_drop by blast
qed

lemma sub_assum1:
  assumes a0: "(\<Gamma>,l0@l1) \<in> assum (p,R)" and a1:"l0\<noteq>[]"
  shows "(\<Gamma>,l0) \<in> assum (p,R)"
  by (metis a0 a1 append_self_conv2 id_take_nth_drop length_greater_0_conv sub_assum take_0)   
 


(* text{* 
@{text rel_safe} specifies that the relation leaves unmodifed any fragment out of the 
state
*}
definition rel_safe:: "(('l::sep_algebra,'g::sep_algebra) transition \<Rightarrow> bool) \<Rightarrow> bool"
where
"rel_safe R \<equiv> \<forall>h h1 h2 t. R (h1,t) \<and> ((h1 \<uplus>\<^sub>p h2) h) \<longrightarrow> R (h, t \<uplus> h2)"

definition mem_safe::
"(('l::sep_algebra,'g::sep_algebra) state,'p,'f) body \<Rightarrow> 
 (('l,'g) state,'p,'f) com \<Rightarrow> 
 (('l,'g) transition \<Rightarrow> bool) \<Rightarrow> 
   bool"
where
 "mem_safe \<Gamma> f R \<equiv> \<forall>h h1 h2 t1. 
      ((\<forall>c\<in> cp \<Gamma> f (Normal h1). 
        final_valid(last (snd c)) \<and> (Normal t1 =  snd (last (snd c))) \<and>
        (\<forall>i. Suc i<length (snd c) \<longrightarrow> 
                 (fst c)\<turnstile>\<^sub>c((snd c)!i)  \<rightarrow>\<^sub>e ((snd c)!(Suc i)) \<longrightarrow>                  
                   (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> 
                     (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (R))) \<and>      
        (h1 \<uplus>\<^sub>p h2) h \<longrightarrow>
        (\<forall>c\<in> cp \<Gamma> f (Normal h). 
          final_valid(last (snd c)) \<and>
          (\<forall>i. Suc i<length (snd c) \<longrightarrow> 
              (fst c)\<turnstile>\<^sub>c((snd c)!i)  \<rightarrow>\<^sub>e ((snd c)!(Suc i)) \<longrightarrow>                  
              (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> 
                (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (R)) \<longrightarrow>
              (Normal (t1 \<uplus> h2) =  snd (last (snd c)))))     
      "                         
 *)

     
subsection \<open>Validity for Parallel Programs.\<close>
definition All_End :: "('s,'p,'f,'e) par_config \<Rightarrow> bool" where
  "All_End xs \<equiv> fst xs \<noteq>[] \<and> (\<forall>i<length (fst xs). final ((fst xs)!i,snd xs))"

definition par_assum :: 
  "('s set \<times>  
   (('s,'f) tran) set) \<Rightarrow>
   (('s,'p,'f,'e) par_confs) set" where
  "par_assum \<equiv> 
     \<lambda>(pre, rely). {c. 
       snd((snd c)!0) \<in> Normal ` pre \<and> (\<forall>i. Suc i<length (snd c) \<longrightarrow> 
       (fst c)\<turnstile>\<^sub>p((snd c)!i)  \<rightarrow>\<^sub>e ((snd c)!(Suc i)) \<longrightarrow>        
         (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> rely)}"
           
definition par_comm :: 
  "((('s,'f) tran) set  \<times> 
     ('s set \<times> 's set))  \<Rightarrow> 
    'f set \<Rightarrow>
   (('s,'p,'f,'e) par_confs) set" where
  "par_comm \<equiv> 
     \<lambda>(guar, (q,a)) F. 
     {c. snd (last (snd c)) \<notin> Fault ` F \<longrightarrow> 
         (\<forall>i. 
            Suc i<length (snd c) \<longrightarrow> 
            (fst c)\<turnstile>\<^sub>p((snd c)!i)  \<rightarrow> ((snd c)!(Suc i)) \<longrightarrow>                        
              (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> guar) \<and> 
                (All_End (last (snd c)) \<longrightarrow> 
                   (\<exists>j<length (fst (last (snd c))). fst (last (snd c))!j=Throw \<and> 
                        snd (last (snd c)) \<in> Normal ` a) \<or>
                   (\<forall>j<length (fst (last (snd c))). fst (last (snd c))!j=Skip \<and>
                        snd (last (snd c)) \<in> Normal ` q))}"

definition par_com_validity :: 
  "('s,'p,'f,'e) body \<Rightarrow> 
   'f set \<Rightarrow>
   ('s,'p,'f,'e) par_com \<Rightarrow>  
   ('s set) \<Rightarrow> 
   ((('s,'f) tran) set) \<Rightarrow> 
   ((('s,'f) tran) set) \<Rightarrow> 
   ('s set) \<Rightarrow>
   ('s set) \<Rightarrow> 
     bool"  
("_ \<Turnstile>\<^bsub>'/_\<^esub>/ _ SAT [_, _, _, _,_]" [61,60,0,0,0,0,0,0] 45) where
  "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Ps SAT [pre, R, G, q,a] \<equiv> 
   \<forall>s. par_cp \<Gamma> Ps s \<inter> par_assum(pre, R)  \<subseteq> par_comm(G, (q,a)) F"
   
definition par_com_cvalidity :: 
  "('s,'p,'f,'e) body \<Rightarrow>
    ('s,'p,'f,'e) sextuple set \<Rightarrow>
   'f set \<Rightarrow>
  ('s,'p,'f,'e) par_com \<Rightarrow>   
   ('s set) \<Rightarrow> 
   ((('s,'f) tran) set) \<Rightarrow> 
   ((('s,'f) tran) set) \<Rightarrow> 
   ('s set) \<Rightarrow>
   ('s set) \<Rightarrow> 
     bool"  
("_,_ \<Turnstile>\<^bsub>'/_\<^esub>/ _ SAT [_, _, _, _,_]" [61,60,0,0,0,0,0,0] 45) where
  "\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Ps SAT [p,  R, G, q,a] \<equiv> 
  (\<forall>(c,p,R,G,q,a)\<in> \<Theta>. (\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a])) \<longrightarrow>
   \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Ps SAT [p, R, G, q,a]"
   
declare Un_subset_iff [simp del] sup.bounded_iff [simp del]

inductive
lrghoare :: "[('s,'p,'f,'e) body,
             ('s,'p,'f,'e) sextuple set,
              'f set,
              ('s,'p,'f,'e) com,  
              ('s set),  
              (('s,'f) tran) set, (('s,'f) tran) set,
              's set,
               's set] \<Rightarrow> bool"
    ("_,_ \<turnstile>\<^bsub>'/_\<^esub> _ sat [_, _, _, _,_]" [61,61,60,60,0,0,0,0] 45)
where
 Skip: "\<lbrakk> Sta q R; (\<forall>s. (Normal s, Normal s) \<in> G) \<rbrakk> \<Longrightarrow>
         \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> Skip sat [q, R, G, q,a] "

|Spec: "\<lbrakk>Sta p R;Sta q R;
        (\<forall>s t. s\<in>p \<and> (s,t)\<in>r \<longrightarrow> (Normal s,Normal t) \<in> G);
         p \<subseteq> {s. (\<forall>t. (s,t)\<in>r \<longrightarrow> t \<in> q) \<and> (\<exists>t. (s,t) \<in> r)} \<rbrakk> \<Longrightarrow> 
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Spec r e) sat [p, R, G, q,a]"

| Basic: "\<lbrakk> Sta p R;Sta q R;
           (\<forall>s t. s\<in>p \<and> (t=f s) \<longrightarrow> (Normal s,Normal t) \<in> G);
            p \<subseteq> {s. f s \<in> q} \<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Basic f e) sat [p, R, G, q,a]"

| If: "\<lbrakk>Sta p R;  (\<forall>s. (Normal s, Normal s) \<in> G); 
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> b, R, G, q,a]; 
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [p \<inter> (-b), R, G, q,a]\<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Cond b c1 c2) sat [p,  R, G, q,a]"

| While: "\<lbrakk> Sta p R; Sta (p \<inter> (-b)) R; Sta a R; (\<forall>s. (Normal s,Normal s) \<in> G);
            \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p \<inter> b, R, G, p,a]\<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (While b c) sat [p, R, G, p \<inter> (-b),a]"

| Seq: "\<lbrakk>Sta a R; Sta p R; (\<forall>s. (Normal s,Normal s) \<in> G); 
         \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p, R, G, q,a]; \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [q, R, G, r,a]\<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Seq c1 c2) sat [p, R, G, r,a]"

| Await: "\<lbrakk> Sta p R; Sta q R; Sta a R;
            \<forall>V. \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
                  (p \<inter> b \<inter> {V}) c 
                  ({s. (Normal V, Normal s) \<in> G} \<inter> q),
                  ({s. (Normal V, Normal s) \<in> G} \<inter> a)\<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Await b c e) sat [p, R, G, q,a]"

| Guard: "\<lbrakk>Sta (p \<inter> g) R; (\<forall>s. (Normal s, Normal s) \<in> G); 
           \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p \<inter> g, R, G, q,a]\<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Guard f g c) sat [p \<inter> g, R, G, q,a]"

| Guarantee:  "\<lbrakk> Sta p R; (\<forall>s. (Normal s, Normal s) \<in> G); f\<in>F;
                 \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p \<inter> g, R, G, q,a] \<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Guard f g c) sat [p, R, G, q,a]"

| CallRec: "\<lbrakk>(c,p,R,G,q,a) \<in> Specs; 
             \<forall>(c,p,R,G,q,a)\<in> Specs. c \<in> dom \<Gamma> \<and> 
              Sta p R \<and> (\<forall>s. (Normal s,Normal s) \<in> G)\<and>  
             \<Gamma>,\<Theta> \<union> Specs \<turnstile>\<^bsub>/F\<^esub> (the (\<Gamma> c)) sat [p,  R, G, q,a];
            Sta p R; (\<forall>s. (Normal s, Normal s) \<in> G)\<rbrakk> \<Longrightarrow>
            \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]" 

| Asm: "\<lbrakk>(c,p,R,G,q,a) \<in> \<Theta>\<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]" 

| Call: "\<lbrakk>
         Sta p R; (\<forall>s. (Normal s, Normal s) \<in> G);c \<in> dom \<Gamma>; 
         \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (the (\<Gamma> c)) sat [p, R, G, q,a]\<rbrakk>  \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]" 

| DynCom: "\<lbrakk>(Sta p R) \<and> (Sta q R) \<and> (Sta a R) \<and>
            (\<forall>s. (Normal s,Normal s) \<in> G);
            (\<forall>s \<in> p. (\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (c s) sat [p, R, G, q,a]))\<rbrakk> \<Longrightarrow>
            \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (DynCom c) sat [p, R, G, q,a]"

| Throw: "\<lbrakk>Sta a R; (\<forall>s. (Normal s, Normal s) \<in> G) \<rbrakk> \<Longrightarrow>
         \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> Throw sat [a,  R, G, q,a] "

| Catch: "\<lbrakk>Sta q R; (\<forall>s. (Normal s, Normal s) \<in> G); 
           \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p, R, G, q,r]; 
           \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [r, R, G, q,a]\<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Catch c1 c2) sat [p, R, G, q,a]"

| Conseq: "\<forall>s \<in> p. 
             (\<exists>p' R' G' q' a' \<Theta>'.  
             (s\<in> p') \<and>
              R \<subseteq> R' \<and>            
             G' \<subseteq> G \<and>             
             q' \<subseteq> q \<and>
             a' \<subseteq> a \<and> \<Theta>' \<subseteq> \<Theta> \<and>                       
            (\<Gamma>,\<Theta>'\<turnstile>\<^bsub>/F\<^esub> P sat [p', R', G', q',a']) ) 
            \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q,a]"

| Conj_post: " \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q,a] \<Longrightarrow>
                \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q',a'] 
            \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q \<inter> q',a \<inter> a']"
  
| Conj_Inter: "sa\<noteq>({}::nat set) \<Longrightarrow> 
               \<forall>i\<in>sa. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q i,a] \<Longrightarrow>                
               \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G,\<Inter>i\<in>sa. q i,a]" 

  
inductive_cases hoare_elim_cases [cases set]:
 "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> Skip sat [p, R, G, q,a]"

thm hoare_elim_cases
(*
lemma "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> Skip sat [p, R, G, q,a] \<Longrightarrow> 
        \<forall>s \<in> p. 
          (\<exists>p' R' G' q' a'.  
           (s\<in> p') \<and>
            R \<subseteq> R' \<and>            
            G' \<subseteq> G \<and>             
            q' \<subseteq> q \<and>
            a' \<subseteq> a \<and>                        
           (\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p', R', G', q',a']) \<and> p'=q' \<and> Sta q' R' \<and> Norm R' \<and> (\<forall>s. (Normal s, Normal s) \<in> G'))"
proof -
  assume a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> Skip sat [p, R, G, q,a]"  
  {
   fix s
   assume a01:"s\<in>p"
   have "(\<exists>p' R' G' q' a'.  
           (s\<in> p') \<and>
            R \<subseteq> R' \<and>            
            G' \<subseteq> G \<and>             
            q' \<subseteq> q \<and>
            a' \<subseteq> a \<and>                        
           (\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p', R', G', q',a']) \<and> p'=q' \<and> Sta q' R' \<and> Norm R' \<and> (\<forall>s. (Normal s, Normal s) \<in> G'))"
   proof (cases "p=q")
    case True thus ?thesis using hoare_elim_cases   sorry
   next
    case False thus ?thesis sorry
   qed
  } thus ?thesis by fastforce
qed*)

(* lemma "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p, R, G, q,r] \<Longrightarrow>
       c\<noteq>Throw \<Longrightarrow>
       Sta p R"
sorry *)
(*
| Env:  "\<lbrakk>noawaits c; \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> (p ) (sequential c) q,(a)\<rbrakk> \<Longrightarrow>
         \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> c sat [p, sep_empty, Emp, Emp, q,a]"
        
| Hide: "\<lbrakk>\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p, (I \<and>* I'), (R \<and>* R'), (G \<and>* G'), q,a]; 
         (I  \<triangleright> R); 
         (I  \<triangleright> G)
          \<rbrakk> \<Longrightarrow> 
         \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> c sat [p, I, R, G, q,a]" 

|Frame: "\<lbrakk>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p, I, R, G , q,a]; 
        I'  \<triangleright> R'; I'  \<triangleright> G';
        Sta r (R'\<and>*tran_Id);
        (\<forall>s t. (r imp (I'\<and>*sep_true))(s,t));
        (rel_safe R); (rel_safe (G\<and>*tran_True)) \<rbrakk>  \<Longrightarrow>
        \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> c sat [p\<and>*r, I \<and>* I', R \<and>* R', G \<and>* G', q\<and>*r,a\<and>*r]"
*)


definition Pre :: " ('s,'p,'f,'e)rgformula \<Rightarrow> ('s set)" where
  "Pre x \<equiv> fst(snd x)"

definition Post :: "('s,'p,'f,'e) rgformula \<Rightarrow> ('s set)" where
  "Post x \<equiv>  fst(snd(snd(snd(snd x))))"

definition Abr ::  "('s,'p,'f,'e) rgformula \<Rightarrow> ('s set)" where
  "Abr x \<equiv> snd(snd(snd(snd(snd x))))"

definition Rely :: "('s,'p,'f,'e) rgformula \<Rightarrow> (('s,'f) tran) set" where
  "Rely x \<equiv> fst(snd(snd x))"

definition Guar ::  "('s,'p,'f,'e) rgformula \<Rightarrow> (('s,'f) tran) set" where
  "Guar x \<equiv> fst(snd(snd(snd x)))"

definition Com :: "('s,'p,'f,'e) rgformula \<Rightarrow> ('s ,'p,'f,'e) com" where
  "Com x \<equiv> fst  x"


inductive
  par_rghoare ::  "[('s,'p,'f,'e) body,
              ('s,'p,'f,'e) sextuple set,
              'f set,
              ( ('s,'p,'f,'e) rgformula) list,  
              's set,              
              (('s,'f) tran) set, (('s,'f) tran) set,
              's set,
               's set] \<Rightarrow> bool"
    ("_,_ \<turnstile>\<^bsub>'/_\<^esub> _ SAT [_, _, _, _,_]" [61,60,60,0,0,0,0] 45)
where
  Parallel:
  "\<lbrakk> \<forall>i<length xs. R \<union> (\<Union>j\<in>{j. j<length xs \<and> j\<noteq>i}. (Guar(xs!j))) \<subseteq> (Rely(xs!i));
    (\<Union>j<length xs. (Guar(xs!j))) \<subseteq> G;
     p \<subseteq> (\<Inter>i<length xs. (Pre(xs!i)));
    (\<Inter>i<length xs. (Post(xs!i))) \<subseteq> q;
    (\<Union>i<length xs. (Abr(xs!i))) \<subseteq> a;                 
    \<forall>i<length xs. \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> Com(xs!i) sat [Pre(xs!i),Rely(xs!i),Guar(xs!i),Post(xs!i),Abr(xs!i)] \<rbrakk>
   \<Longrightarrow>  \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> xs SAT [p, R, G, q,a]" 
 
section {* Soundness *}

lemma skip_suc_i:
  assumes a1:"(\<Gamma>, l) \<in> cptn \<and> fst (l!i) = Skip"   
  assumes a2:"i+1 < length l"
  shows "fst (l!(i+1)) = Skip"
proof -
  from a2 a1 obtain l1 ls where "l=l1#ls" 
    by (metis list.exhaust list.size(3) not_less0) 
  then have "\<Gamma>\<turnstile>\<^sub>c (l!i) \<rightarrow>\<^sub>c\<^sub>e (l!(Suc i))" using cptn_stepc_rtran a1 a2
    by fastforce 
  thus ?thesis using a1 a2 step_ce_elim_cases
    by (metis (no_types) Suc_eq_plus1 not_eq_not_env prod.collapse stepc_elim_cases(1))
qed 

lemma throw_suc_i:
  assumes a1:"(\<Gamma>, l) \<in> cptn \<and> (fst(l!i) = Throw \<and> snd(l!i) = Normal s1)"   
  assumes a2:"Suc i < length l"
  assumes a3:"env_tran_right \<Gamma> l rely \<and> Sta q rely \<and> s1 \<in> q"
  shows "fst (l!(Suc i)) =  Throw \<and> (\<exists>s2. snd(l!(Suc i)) = Normal s2 \<and> s2 \<in>q)"
proof -
  have fin:"final (l!i)" using a1 unfolding final_def by auto 
  from a2 a1 obtain l1 ls where "l=l1#ls" 
    by (metis list.exhaust list.size(3) not_less0) 
  then have "\<Gamma>\<turnstile>\<^sub>c (l!i) \<rightarrow>\<^sub>c\<^sub>e (l!(Suc i))" using cptn_stepc_rtran a1 a2
    by fastforce then have "\<Gamma>\<turnstile>\<^sub>c (l!i) \<rightarrow> (l!(Suc i)) \<or> \<Gamma>\<turnstile>\<^sub>c (l!i) \<rightarrow>\<^sub>e (l!(Suc i))"
    using step_ce_elim_cases by blast
  thus ?thesis proof                                          
    assume "\<Gamma>\<turnstile>\<^sub>c (l!i) \<rightarrow> (l!(Suc i))" thus ?thesis using fin no_step_final' by blast
  next
    assume "\<Gamma>\<turnstile>\<^sub>c (l!i) \<rightarrow>\<^sub>e (l!(Suc i))" thus ?thesis 
      using a1 a3 a2 env_tran_normal by (metis (no_types, lifting)  env_c_c' prod.collapse) 
  qed 
qed 

lemma i_skip_all_skip:assumes a1:"(\<Gamma>, l) \<in> cptn \<and> fst (l!i) = Skip"
      assumes a2: "i\<le>j \<and> j < (length l)"
      assumes a3:"n=j-i"
      (* assumes a4:"env_tran_right \<Gamma> l rely" *)
      shows "fst (l!j) = Skip"
using a1 a2 a3
proof (induct n arbitrary: i j)
  case 0
  then have "Suc i = Suc j" by simp  
  thus ?case using "0.prems" skip_suc_i by fastforce
next
  case (Suc n)    
  then have "length l > Suc i" by auto 
  then have "i<j" using Suc by fastforce
  moreover then have "j-1< length l" using Suc by fastforce
  moreover then have "j  - i = Suc n" using Suc by fastforce
  ultimately have "fst (l ! (j)) = LanguageCon.com.Skip" using Suc  skip_suc_i
    by (metis (no_types, lifting) Suc_diff_Suc Suc_eq_plus1 Suc_leI `Suc i < length l` diff_Suc_1)        
  also have "j=j" using Cons using Suc.prems(2) by linarith  
  ultimately show ?case using Suc by (metis (no_types))
qed

lemma i_throw_all_throw:assumes a1:"(\<Gamma>, l) \<in> cptn \<and> (fst (l!i) = Throw \<and> snd (l!i) = Normal s1)"
      assumes a2: "i\<le>j \<and> j < (length l)"
      assumes a3:"n=j-i"
      assumes a4:"env_tran_right \<Gamma> l rely \<and> Sta q rely \<and> s1\<in>q" 
      shows "fst (l!j) = Throw \<and> (\<exists>s2. snd(l!j) = Normal s2  \<and> s2\<in>q)"
using a1 a2 a3 a4
proof (induct n arbitrary: i j s1)
  case 0
  then have "Suc i = Suc j" by simp  
  thus ?case using "0.prems" skip_suc_i by fastforce
next
  case (Suc n)    
  then have l_suc:"length l > Suc i" by linarith 
  then have "i<j" using Suc.prems(3) by linarith 
  moreover then have "j-1< length l" by (simp add: Suc.prems(2) less_imp_diff_less) 
  moreover then have "j - Suc i = n" by (metis Suc_diff_Suc Suc_inject \<open>i < j\<close> Suc(4))
  ultimately obtain s2 where "fst (l ! (j-1)) = LanguageCon.com.Throw \<and> snd (l ! (j-1)) = Normal s2 \<and> s2\<in>q"
    using Suc(1)[of i s1 "j-1"] Suc(2) Suc(5)
    by (metis (no_types, lifting) Suc_diff_Suc diff_Suc_eq_diff_pred diff_zero less_imp_Suc_add not_le not_less_eq_eq zero_less_Suc) 
  also have "Suc (j - 1) < length l" using Suc by arith
  ultimately have "fst (l ! (j)) = LanguageCon.com.Throw \<and> (\<exists>s2. snd(l!j) = Normal s2 \<and> s2\<in>q)" 
    using Suc(2-5) throw_suc_i[of \<Gamma> l "j-1" s2 rely q] a4
    by fastforce
  also have "j=j" using Cons using Suc.prems(2) by linarith  
  ultimately show ?case using Suc by (metis (no_types))
qed    

lemma only_one_component_tran_j:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!i) = Skip  \<or> fst (l!i) = Throw " and 
         a1': "snd (l!i) = Normal x \<and> x \<in> q" and
         a2: "i\<le>j \<and> Suc j < length l" and
         a3: "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" and 
         a4: "env_tran_right \<Gamma> l rely \<and> Sta q rely"    
   shows "P"
proof -   
   have "fst (l!j) = Skip  \<or> (fst (l!i) = Throw \<and> snd(l!i) = Normal x)" 
   using a0 a1 a1' a2 a3 a4 i_skip_all_skip by fastforce           
   also have "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" using a3 by fastforce 
   ultimately show ?thesis
by (meson SmallStepCon.final_def SmallStepCon.no_step_final' Suc_lessD a0 a2  a4 i_throw_all_throw a1')  
qed     

lemma only_one_component_tran_all_j:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!i) = Skip  \<or> (fst (l!i) = Throw \<and> snd(l!i) = Normal s1)" and 
         a1': "snd (l!i) = Normal x \<and> x \<in> q" and
         a2: "Suc i<length l" and
         a3: "\<forall>j. i\<le>j \<and> Suc j < length l \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"  and
         a4: "env_tran_right \<Gamma> l rely \<and> Sta q rely"              
   shows "P" 
using a0 a1 a2 a3 a4 a1' only_one_component_tran_j 
by (metis lessI less_Suc_eq_le) 


lemma zero_skip_all_skip: 
      assumes a1:"(\<Gamma>, l) \<in> cptn \<and> fst (l!0) = Skip \<and>  i < length l"
      shows "fst (l!i) = Skip"
using a1 i_skip_all_skip by blast

lemma all_skip:
   assumes
      a0:"(\<Gamma>,x)\<in>cptn" and
      a1:"x!0 = (Skip,s)"
shows "(\<forall>i<length x. fst(x!i) = Skip)"
using a0 a1 zero_skip_all_skip by fastforce

lemma zero_throw_all_throw:
      assumes a1:"(\<Gamma>, l) \<in> cptn \<and> fst (l!0) = Throw \<and> 
                  snd(l!0) = Normal s1 \<and>  i < length l \<and> s1\<in>q"
      assumes a2: "env_tran_right \<Gamma> l rely \<and> Sta q rely" 
      shows "fst (l!i) = Throw \<and> (\<exists>s2. snd (l!i) = Normal s2)"
using a1 a2 i_throw_all_throw by (metis le0) 

lemma only_one_component_tran_0:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "(fst (l!0) = Skip) \<or> (fst (l!0) = Throw)" and                  
         a1': "snd (l!0) = Normal x \<and> x \<in> q" and
         a2: "Suc j < length l" and
         a3: "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"  and
         a4: "env_tran_right \<Gamma> l rely \<and> Sta q rely"         
   shows "P"      
  proof-
   have a2':"0\<le>j \<and> Suc j<length l" using a2 by arith
   show ?thesis 
   using only_one_component_tran_j[OF a0 a1 a1' a2' a3 a4] by auto
qed

lemma not_step_comp_step_env:
 assumes a0:  "(\<Gamma>, l) \<in> cptn" and
         a1: "(Suc j<length l)" and 
         a2: "(\<forall>k < j. \<not>((\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))))"
  shows "(\<forall>k < j. ((\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))))"
proof -
  {fix k
   assume asm: "k<j"
   also then have "Suc k<length l" using a1 a2 by auto
   ultimately have "(\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>c\<^sub>e (l!(Suc k)))" using a0 cptn_stepc_rtran
  proof -
    obtain nn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
      f1: "\<forall>x0 x1. (\<exists>v2>x1. x0 = Suc v2) = (x1 < nn x0 x1 \<and> x0 = Suc (nn x0 x1))"
      by moura
    obtain pp :: "nat \<Rightarrow> (('b, 'a, 'c,'d) LanguageCon.com \<times> ('b, 'c) xstate) list \<Rightarrow> 
                 ('b, 'a, 'c,'d) LanguageCon.com \<times> ('b, 'c) xstate" and 
           pps :: "nat \<Rightarrow> (('b, 'a, 'c,'d) LanguageCon.com \<times> ('b, 'c) xstate) list \<Rightarrow> 
                  (('b, 'a, 'c,'d) LanguageCon.com \<times> ('b, 'c) xstate) list" where
      "\<forall>x0 x1. (\<exists>v2 v3. x1 = v2 # v3 \<and> length v3 = x0) = (x1 = pp x0 x1 # pps x0 x1 \<and> length (pps x0 x1) = x0)"
      by moura
    then have f2: "l = pp (nn (length l) k) l # pps (nn (length l) k) l \<and> length (pps (nn (length l) k) l) = nn (length l) k"
      using f1 by (meson Suc_lessE \<open>Suc k < length l\<close> length_Suc_conv)
    then have f3: "Suc k < length (pp (nn (length l) k) l # pps (nn (length l) k) l)"
      by (metis \<open>Suc k < length l\<close>)
    have "(\<Gamma>, pp (nn (length l) k) l # pps (nn (length l) k) l) \<in> cptn"
      using f2 a0 by presburger
    then have "\<Gamma>\<turnstile>\<^sub>c (pp (nn (length l) k) l # pps (nn (length l) k) l) ! k \<rightarrow>\<^sub>c\<^sub>e (pp (nn (length l) k) l # pps (nn (length l) k) l) ! Suc k"
      using f3 by (meson cptn_stepc_rtran)
    then show ?thesis
      using f2 by auto
  qed 
   also have "\<not>((\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))))" using a2 asm by auto
   ultimately have "((\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))" using step_ce_elim_cases by blast
  } thus ?thesis by auto
qed

lemma cptn_i_env_same_prog:
assumes a0: "(\<Gamma>, l) \<in> cptn" and
        a1:  "\<forall>k < j. k\<ge>i \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))" and
        a2: "i\<le>j \<and> j < length l"
shows "fst (l!j) =  fst (l!i)"
using a0 a1 a2
proof (induct "j-i" arbitrary: l j i)
  case 0 thus ?case by auto    
next
  case (Suc n)     
    then have lenl:"length l>Suc 0" by fastforce    
    have "j>0" using Suc by linarith
    then obtain j1 where prev:"j=Suc j1" 
      using not0_implies_Suc by blast     
    then obtain a0 a1 l1 where l:"l=a0#l1@[a1]" 
    using Suc lenl by (metis add.commute add.left_neutral length_Cons list.exhaust list.size(3) not_add_less1 rev_exhaust)     
    then have al1_cptn:"(\<Gamma>,a0#l1)\<in> cptn"
      using Suc.prems(1) Suc.prems(3) tl_in_cptn cptn_dest_2
      by blast
    have i_j:"i\<le>j1" using Suc prev by auto
    have "\<forall>k < j1. k\<ge>i \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c((a0#l1)!k)  \<rightarrow>\<^sub>e ((a0#l1)!(Suc k)))"
    proof -
       {fix k
        assume a0:"k<j1 \<and> k\<ge>i"
        then have "(\<Gamma>\<turnstile>\<^sub>c((a0#l1)!k)  \<rightarrow>\<^sub>e ((a0#l1)!(Suc k)))" 
        using  l Suc(4) prev lenl Suc(5)
        proof -   
          have suc_k_j:"Suc k < j" using a0 prev by blast
          have j1_l_l1:"j1 < Suc (length l1)" 
            using Suc.prems(3) l prev by auto
          have "k < Suc j1"
            using `k < j1 \<and> i \<le> k` less_Suc_eq by blast
          hence f3: "k < j"
            using prev by blast
          hence ksuc:"k < Suc (Suc j1)"
            using less_Suc_eq prev by blast
          hence f4: "k < Suc (length l1)"
            using  prev Suc.prems(3) l a0 j1_l_l1 less_trans 
            by blast            
          have f6: "\<Gamma>\<turnstile>\<^sub>c l ! k \<rightarrow>\<^sub>e (l ! Suc k)"
            using f3 Suc(4) a0 by blast
          have k_l1:"k < length l1"
            using f3 Suc.prems(3) i_j l suc_k_j  by auto                            
          thus ?thesis
          proof (cases k)
            case 0 thus ?thesis using f6 l  k_l1
                by (simp add: nth_append)
          next  
            case (Suc k1) thus ?thesis 
              using f6  f4 l k_l1 
              by (simp add: nth_append)
          qed
        qed
       }thus ?thesis by auto
    qed
    then have fst:"fst ((a0#l1)!i)=fst ((a0#l1)!j1)"
      using Suc(1)[of j1 i "a0#l1"] 
            Suc(2) Suc(3) Suc(4) Suc(5) prev al1_cptn i_j
      by (metis (mono_tags, lifting) Suc_diff_le Suc_less_eq diff_Suc_1 l length_Cons length_append_singleton)
    have len_l:"length l = Suc (length (a0#l1))" using l by auto
    then have f1:"i<length (a0#l1)" using Suc.prems(3) i_j prev by linarith
    then have f2:"j1<length (a0#l1)" using Suc.prems(3) len_l prev by auto
    have i_l:"fst (l!i) = fst ((a0#l1)!i)" 
      using l prev f1 f2 fst 
      by (metis (no_types) append_Cons nth_append)
    also have j1_l:"fst (l!j1) = fst ((a0#l1)!j1)"
    using l prev f1 f2 fst 
      by (metis (no_types) append_Cons nth_append)
    then have "fst (l!i) = fst (l!j1)" using
      i_l j1_l fst by auto      
    thus ?case using Suc prev by (metis env_c_c' i_j lessI prod.collapse)          
qed  
  

lemma cptn_tran_ce_i: 
   assumes a1:"(\<Gamma>, l) \<in> cptn  \<and>  i + 1 < length l"
   shows "\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>c\<^sub>e (l!(Suc i))"
proof -
  from a1
  obtain a1 l1 where "l=a1#l1" using cptn.simps by blast
  thus  ?thesis using a1 cptn_stepc_rtran by fastforce
qed

lemma zero_final_always_env_0: 
      assumes a1:"(\<Gamma>, l) \<in> cptn" and
              a2: "fst (l!0) = Skip \<or> fst (l!0) = Throw" and
              a2': "snd(l!0) = Normal s1 \<and> s1\<in>q" and
              a3: "Suc i < length l" and
              a4: "env_tran_right \<Gamma> l rely \<and> Sta q rely"
      shows "\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))"
proof -
   have "\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>c\<^sub>e (l!(Suc i))" using a1 a2 a3 cptn_tran_ce_i by auto   
   also have "\<not> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" using a1 a2 a3 a4 a2'
     using only_one_component_tran_0 by metis           
   ultimately show ?thesis by (simp add: step_ce.simps) 
qed

lemma final_always_env_i: 
      assumes a1:"(\<Gamma>, l) \<in> cptn" and
              a2: "fst (l!0) = Skip \<or> fst (l!0) = Throw" and
              a2': "snd(l!0) = Normal s1 \<and> s1\<in>q" and
              a3: "j\<ge>i \<and> Suc j<length l" and
              a4: "env_tran_right \<Gamma> l rely \<and> Sta q rely"
      shows "\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j))"
proof -
   have ce_tran:"\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>c\<^sub>e (l!(Suc j))" using a1 a2 a3 a4 cptn_tran_ce_i by auto   
   then have "\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)) \<or> \<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))" 
     using step_ce_elim_cases by blast
   thus ?thesis
   proof
     assume "\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j))" then show ?thesis by auto
   next
     assume a01:"\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))"
      then  have "\<not> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"   
        using a1 a2 a3 a4 a2' only_one_component_tran_j [OF a1]  
        by blast
      then show ?thesis using a01 ce_tran by (simp add: step_ce.simps) 
   qed
qed


subsection {*Skip Sound*}

lemma stable_q_r_q: 
  assumes a0:"Sta q R"  and       
          a1: "snd(l!i) \<in> Normal ` q" and
          a2:"(snd(l!i), snd(l!(Suc i))) \<in> R"
  shows "snd(l!(Suc i)) \<in> Normal ` q"
using a0  a1  a2 
unfolding Sta_def  by fastforce 

lemma stability:
assumes   a0:"Sta q R"  and                 
          a1: "snd(l!j) \<in> Normal ` q" and
          a2: "j\<le>k \<and> k < (length l)" and
          a3: "n=k-j" and
          a4: "\<forall>i. j\<le>i \<and> i < k \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))" and
          a5:"env_tran_right \<Gamma> l R "
      shows "snd (l!k) \<in> Normal ` q \<and> fst (l!j) = fst (l!k)"
using a0 a1 a2 a3 a4 a5 
proof (induct n arbitrary: j k)
  case 0
    thus ?case by auto
next
  case (Suc n) 
    then have "length l > j + 1" by arith     
    moreover then have "k-1< length l" using Suc by fastforce    
    moreover then have "(k - 1) - j = n" using Suc by fastforce
    moreover then have  "j\<le>k-1" using Suc by arith 
    moreover have "\<forall>i. j \<le> i \<and> i < k-1 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c (l ! i) \<rightarrow>\<^sub>e (l ! Suc i)"
      using Suc by fastforce    
    ultimately have induct:"snd (l! (k-1)) \<in> Normal ` q \<and> fst (l!j) = fst (l!(k-1))" using Suc
      by blast      
    also have j_1:"k-1+1=k" using Cons Suc.prems(4) by auto 
    have f1:"\<forall>i. j\<le>i \<and> i < k \<longrightarrow> (snd((snd (\<Gamma>,l))!i), snd((snd (\<Gamma>,l))!(Suc i))) \<in>  R"
    using Suc unfolding env_tran_right_def by fastforce
    have  k1:"k - 1 < k"
      by (metis (no_types) Suc_eq_plus1 j_1 lessI)    
    then have "(snd((snd (\<Gamma>,l))!(k-1)), snd((snd (\<Gamma>,l))!(Suc (k-1)))) \<in>  R"    
    using `j \<le> k - 1` f1 by blast                           
    ultimately have "snd (l!k) \<in> Normal ` q" using stable_q_r_q Suc(2)  Suc(5)  by fastforce
    also have "fst (l!j) = fst (l!k)"
    proof -
      have "\<Gamma>\<turnstile>\<^sub>c (l ! (k-1)) \<rightarrow>\<^sub>e (l ! k)" using Suc(6) k1 `j\<le>k-1` by fastforce
      thus ?thesis using k1 prod.collapse env_c_c' induct by metis
    qed
    ultimately show ?case by meson
qed

lemma stable_only_env_i_j: 
  assumes a0:"Sta q R"  and                 
          a1: "snd(l!i) \<in> Normal ` q" and
          a2: "i<j \<and> j < (length l)" and
          a3: "n=j-i-1" and
          a4: "\<forall>k\<ge>i. k < j \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))" and
          a5: "env_tran_right \<Gamma> l R"
      shows "snd (l!j) \<in> Normal ` q"
using a0 a1 a2 a3 a4 a5  by (meson less_imp_le_nat  stability)

  
lemma stable_only_env_1: 
  assumes a0:"Sta q R"  and                 
          a1: "snd(l!i) \<in> Normal ` q" and
          a2: "i<j \<and> j < (length l)" and
          a3: "n=j-i-1" and
          a4: "\<forall>i. Suc i < length l \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))" and
          a5: "env_tran_right \<Gamma> l R"
      shows "snd (l!j) \<in> Normal ` q"
using a0 a1 a2 a3 a4 a5 
by (meson stable_only_env_i_j less_trans_Suc)


lemma stable_only_env_q: 
  assumes a0:"Sta q R"  and                 
          a1: "\<forall>i. Suc i < length l \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))" and
          a2: "env_tran \<Gamma> q l R"
      shows "\<forall>i. i < length l \<longrightarrow> snd (l!i) \<in> Normal ` q"
proof (cases "0 < length l")
  case False thus ?thesis using a2 unfolding env_tran_def by fastforce 
next
  case True 
  thus ?thesis 
  proof - {
    fix i
    assume aa1:"i < length l"
    have post_0:"snd (l ! 0) \<in> Normal ` q " 
      using a2 unfolding env_tran_def by auto
    then have "snd (l ! i) \<in> Normal ` q"     
    proof (cases i) 
      case 0 thus ?thesis using post_0 by auto
    next
      case (Suc n) 
      
      have "env_tran_right \<Gamma> l R" 
        using a2 env_tran_right_def unfolding env_tran_def by auto
      also have "0<i" using Suc by auto
      ultimately show ?thesis 
        using post_0 stable_only_env_1  a0 a1 a2 aa1  by blast
    qed
  } then show ?thesis by auto qed
qed



lemma Skip_sound1: 
  assumes a0:"Sta q R" and
   a1:"(\<forall>s. (Normal s, Normal s) \<in> G)" and
   a10:"c \<in> cp \<Gamma> Skip s" and
   a11:"c \<in> assum(q, R)" 
   shows "c \<in> comm (G, (q,a)) F"
proof -  
  obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce  
  { 
    assume "snd (last l) \<notin> Fault ` F"
    have cp:"l!0=(Skip,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce   
    have assum:"snd(l!0) \<in> Normal ` q \<and> (\<forall>i. Suc i<length l \<longrightarrow>
             (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
               (snd(l!i), snd(l!(Suc i))) \<in> R)" 
      using a11 c_prod unfolding assum_def by simp
    have concl:"(\<forall>i. Suc i<length l \<longrightarrow> 
           \<Gamma>1\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow>                             
             (snd(l!i), snd(l!(Suc i))) \<in> G)"
    proof -
    { fix i
      assume asuc:"Suc i<length l"        
      then have "\<not> (\<Gamma>1\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))"
        by (metis Suc_lessD cp prod.collapse prod.sel(1) stepc_elim_cases(1) zero_skip_all_skip)
    } thus ?thesis by auto qed
    have concr:"(final (last l)  \<longrightarrow>                    
               ((fst (last l) = Skip \<and> 
                snd (last l) \<in> Normal ` q)) \<or>
                (fst (last l) = Throw \<and> 
                snd (last l) \<in> Normal ` (a)))"
    proof-
    { 
      assume valid:"final (last l)"
      have len_l:"length l > 0" using cp using cptn.simps by blast 
      then obtain a l1 where l:"l=a#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
      have last_l:"last l = l!(length l-1)"
        using last_length [of a l1] l by fastforce
      then have fst_last_skip:"fst (last l) = Skip"             
        by (metis `0 < length l` cp diff_less fst_conv zero_less_one zero_skip_all_skip)                           
      have last_q: "snd (last l) \<in> Normal ` q"    
      proof -
        have env: "env_tran \<Gamma> q l R" using env_tran_def assum cp by blast
        have env_right:"env_tran_right \<Gamma> l R " using  a0 env_tran_right_def assum cp by metis
        also obtain s1 where "snd(l!0) = Normal s1 \<and> s1\<in>q" 
          using assum by auto
        ultimately have all_tran_env: "\<forall>i. Suc i < length l \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))"
          using final_always_env_i cp zero_final_always_env_0 a0
          by fastforce
        then have "\<forall>i. i < length l \<longrightarrow> snd (l!i) \<in> Normal ` q"
          using stable_only_env_q  a0  env  by fastforce
        thus ?thesis using last_l using len_l by fastforce    
      qed
      note res = conjI [OF fst_last_skip last_q]
    } thus ?thesis by auto 
    qed
    note res = conjI [OF concl concr]               
  } thus ?thesis using c_prod unfolding comm_def by auto 
qed


lemma Skip_sound: 
  "Sta q R \<Longrightarrow>       
   (\<forall>s. (Normal s, Normal s) \<in> G)  \<Longrightarrow>
   \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> Skip sat [q,R, G, q,a]" 
proof-
  assume
  a0:"Sta q R" and    
  a1:"(\<forall>s. (Normal s, Normal s) \<in> G)"
  {
    fix s
    have ass:"cpn n \<Gamma> Skip s \<inter> assum(q, R) \<subseteq> comm(G, (q,a)) F"
    proof-      
    { fix c
      assume a10:"c \<in> cpn n \<Gamma> Skip s" and a11:"c \<in> assum(q, R)"
      then have a10:"c\<in>cp \<Gamma> Skip s"
        using cp_def cpn_def cptn_if_cptn_mod cptn_mod_nest_cptn_mod by blast
      have "c\<in>comm(G, (q,a)) F" using Skip_sound1[OF a0 a1 a10 a11] by auto      
    } thus ?thesis by auto
    qed 
  } 
  thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed

lemma Throw_sound1: 
  assumes a1:"Sta a R" and
   a2:"(\<forall>s. (Normal s, Normal s) \<in> G)" and
   a10:"c \<in> cp \<Gamma> Throw s" and
   a11:"c \<in> assum(a, R)"
shows "c \<in> comm (G, (q,a)) F"
proof -  
  obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce     
  {
    assume "snd (last l) \<notin> Fault ` F"
    have cp:"l!0=(Throw,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
    have assum:"snd(l!0) \<in> Normal ` (a) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
             (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
               (snd(l!i), snd(l!(Suc i))) \<in> (R))" 
      using a11 c_prod unfolding assum_def by simp
    then have env_tran:"env_tran_right \<Gamma> l R" using cp env_tran_right_def by auto
    obtain a1 where a_normal:"snd(l!0) = Normal a1 \<and> a1 \<in> a"
      using assum by auto
    have concl:"(\<forall>i ns ns'. Suc i<length l \<longrightarrow> 
           \<Gamma>1\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow>                                           
             (snd(l!i), snd(l!(Suc i))) \<in>  (G))"
    proof -
    { fix i
      assume asuc:"Suc i<length l"
      then have asuci:"i<length l" by fastforce
      then have "fst (l ! 0) = LanguageCon.com.Throw" using cp by auto
      moreover obtain s1 where "snd (l ! 0) = Normal s1" using assum by auto
      ultimately have "fst (l ! i) = Throw \<and> (\<exists>s2. snd (l ! i) = Normal s2)"      
        using cp a1 assum a_normal env_tran asuci zero_throw_all_throw
        by fastforce
      then have "\<not> (\<Gamma>1\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))"
        by (meson SmallStepCon.final_def SmallStepCon.no_step_final')           
    } thus ?thesis by auto qed
    have concr:"(final (last l)  \<longrightarrow>                    
               ((fst (last l) = Skip \<and> 
                snd (last l) \<in> Normal ` q)) \<or>
                (fst (last l) = Throw \<and> 
                snd (last l) \<in> Normal ` (a)))"
    proof-
    { 
      assume valid:"final (last l)"
      have len_l:"length l > 0" using cp using cptn.simps by blast 
      then obtain a1 l1 where l:"l=a1#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
      have last_l:"last l = l!(length l-1)"
        using last_length [of a1 l1] l by fastforce
      then have fst_last_skip:"fst (last l) = Throw"
        by (metis a1 a_normal cp diff_less env_tran fst_conv len_l zero_less_one zero_throw_all_throw)                        
      have last_q: "snd (last l) \<in> Normal ` (a)"    
      proof -
        have env: "env_tran \<Gamma> a l R" using env_tran_def assum cp by blast
        have env_right:"env_tran_right \<Gamma> l R" using env_tran_right_def assum cp by metis
        then have all_tran_env: "\<forall>i. Suc i < length l \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))"
        using final_always_env_i a1 assum cp zero_final_always_env_0 by fastforce            
        then have "\<forall>i. i < length l \<longrightarrow> snd (l!i) \<in> Normal ` (a)"
        using stable_only_env_q  a1  env by fastforce
        thus ?thesis using last_l using len_l by fastforce    
      qed                
      note res = conjI [OF fst_last_skip last_q]
    } thus ?thesis by auto qed
    note res = conjI [OF concl concr]               
   }              
   thus ?thesis using c_prod unfolding comm_def by auto 
qed          

lemma Throw_sound: 
  "Sta a R  \<Longrightarrow>
   (\<forall>s. (Normal s, Normal s) \<in> G) \<Longrightarrow>
   \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> Throw sat [a, R, G, q,a]"
proof -  
 assume   
    a1:"Sta a R" and
    a2:" (\<forall>s. (Normal s, Normal s) \<in> G)" {
    fix s
    have ass:"cpn n \<Gamma> Throw s \<inter> assum(a, R) \<subseteq> comm(G, (q,a)) F"
    proof-      
    { fix c
      assume a10:"c \<in> cpn n \<Gamma> Throw s" and a11:"c \<in> assum(a, R)"
      then have a10:"c\<in>cp \<Gamma> Throw s"
        using cp_def cpn_def cptn_if_cptn_mod cptn_mod_nest_cptn_mod by blast
      have "c\<in>comm(G, (q,a)) F" using Throw_sound1[OF a1 a2 a10 a11] by auto      
    } thus ?thesis by auto
    qed 
  } 
  thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed

lemma no_comp_tran_before_i_0_g:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!0) = c " and         
         a2: "Suc i<length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "j < i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" and
         a4: "\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))" and
         a5: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c, s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> 
                        (c1=Skip) \<or> (c1=Throw \<and> (\<exists>s21. s2 = Normal s21))" and        
         a6: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!0) \<in> Normal ` p \<and> 
                                        Sta q rely \<and> snd (l!Suc j) \<in> Normal ` q"
   shows "P"
  proof -
   have "Suc j < length l" using a0 a1 a2 a3 a4 by fastforce
   then have "fst (l!j) = c" 
     using a0 a1 a2 a3 a4 cptn_env_same_prog[of \<Gamma> l j] by fastforce
   then obtain s s1 c1 where l_0: "l!j = (c, s) \<and> l!(Suc j) = (c1,s1)"  
     by (metis (no_types) prod.collapse)    
   moreover have "snd (l!j) \<in> Normal ` p" using a4 stability[of p rely l 0 j j] a6 a3 a2
    proof -
      have "\<forall>B r ps n na nb f. \<not> Sta B r \<or> snd (ps ! n) \<notin> Normal ` B \<or> \<not> n \<le> na \<or> \<not> na < length ps \<or> na - n \<noteq> nb \<or> (\<exists>nb\<ge>n. nb < na \<and> \<not> f\<turnstile>\<^sub>c ps ! nb \<rightarrow>\<^sub>e ps ! Suc nb) \<or> \<not> env_tran_right f ps r \<or> snd (ps ! na) \<in> Normal ` B \<and> (fst (ps ! n)::('b, 'a, 'c,'d) LanguageCon.com) = fst (ps ! na)"
        using stability by blast
      then show ?thesis
        using Suc_lessD \<open>Suc j < length l\<close> a4 a6 by blast
    qed      
   then have suc_0_skip: "(fst (l!Suc j) = Skip \<or> fst (l!Suc j) = Throw) \<and> 
                           (\<exists>s2. snd(l!Suc j) = Normal s2 ) " 
      using a5 a6 a3 SmallStepCon.step_Stuck_prop using fst_conv imageE l_0 snd_conv by auto 
   thus ?thesis using only_one_component_tran_j
    proof -
      have "\<forall>n na. \<not> n < na \<or> Suc n \<le> na"
        using Suc_leI by satx  
      thus ?thesis using only_one_component_tran_j[OF a0] suc_0_skip a6 a0 a2 a3
        using imageE by blast          
    qed
qed

lemma no_comp_tran_before_i:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = c" and        
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "k\<le>j \<and> j < i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" and
         a4: "\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))" and
          a5: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c, s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> 
                        (c1=Skip) \<or> (c1=Throw \<and> (\<exists>s21. s2 = Normal s21))" and        
         a6: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!0) \<in> Normal ` p \<and> 
                                        Sta q rely \<and> snd (l!Suc j) \<in> Normal ` q"
   shows "P"
using a0 a1 a2 a3 a4 a5 a6
proof (induct k arbitrary: l i j)
  case 0 thus ?thesis using no_comp_tran_before_i_0_g by blast
next
  case (Suc n) 
  then obtain a1 l1 where l: "l=a1#l1"
    by (metis less_nat_zero_code list.exhaust list.size(3))
  then have l1notempty:"l1\<noteq>[]" using Suc by force    
  then obtain i' where i': "i=Suc i'" using Suc 
    using less_imp_Suc_add by blast
  then obtain j' where j': "j=Suc j'" using Suc
    using Suc_le_D by blast      
  have "(\<Gamma>,l1)\<in>cptn" using Suc l
    using tl_in_cptn l1notempty by blast
  moreover have "fst (l1 ! n) = c"
    using Suc l l1notempty by force  
  moreover have "Suc i' < length l1 \<and> n \<le> i' \<and> \<Gamma>\<turnstile>\<^sub>c l1 ! i' \<rightarrow> (l1 ! Suc i')"
    using Suc l l1notempty i' by auto
  moreover have "n \<le> j' \<and> j' < i' \<and> \<Gamma>\<turnstile>\<^sub>c l1 ! j' \<rightarrow> (l1 ! Suc j')"
    using Suc l l1notempty i' j' by auto
  moreover have "\<forall>k<j'. \<Gamma>\<turnstile>\<^sub>c l1 ! k \<rightarrow>\<^sub>e (l1 ! Suc k)"
    using Suc l l1notempty j' by auto     
  moreover have "env_tran_right \<Gamma> l1 rely \<and> Sta q rely \<and> Sta p rely \<and> snd (l1!0) \<in> Normal ` p \<and> 
                                        Sta q rely \<and> snd (l1!Suc j') \<in> Normal ` q" 
  proof -
    have suc0:"Suc 0 < length l" using Suc by auto
    have "j>0" using j' by auto
    then have "\<Gamma>\<turnstile>\<^sub>c(l!0)  \<rightarrow>\<^sub>e (l!(Suc 0))" using Suc(6) by blast
    then have "(snd(l!Suc 0) \<in> Normal ` p)" 
      using Suc(8) suc0 unfolding Sta_def env_tran_right_def by blast
    also have "snd (l!Suc j) \<in> Normal ` q" using Suc(8) by auto
    ultimately show ?thesis using Suc(8) l by (metis env_tran_tail j' nth_Cons_Suc) 
  qed
  ultimately show ?case using Suc(1)[of l1 i' j' ]  Suc(7)  Suc(8) j' l by auto
qed

lemma exists_first_occ: "P (n::nat) \<Longrightarrow> \<exists>m. P m \<and> (\<forall>i<m. \<not> P i)"
proof (induct n)
  case 0 thus ?case by auto
next
  case (Suc n) thus ?case
  by (metis ex_least_nat_le not_less0) 
qed

lemma exist_first_comp_tran':
assumes a1: "Suc i<length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))"      
shows "\<exists>j. (Suc j<length l \<and>  (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))) \<and> (\<forall>k < j. \<not>\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
proof -
  let ?P =  "(\<lambda>n. Suc n<length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!n)  \<rightarrow> (l!(Suc n))))"
  show ?thesis using exists_first_occ[of ?P i] a1 by auto  
qed

lemma exist_first_comp_tran:
assumes a0:"(\<Gamma>, l) \<in> cptn" and
        a1: "Suc i<length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))"      
shows "\<exists>j. j\<le>i \<and>  (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<and> (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
proof -
  obtain j where  pj:"(Suc j<length l \<and>  (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))) \<and> 
                     (\<forall>k < j. \<not>(Suc k<length l \<and>  (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))))"
    using a1 exist_first_comp_tran' by blast
  then have "j\<le>i" using a1 pj by (cases "j\<le>i", auto)
  moreover have "\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))" using pj by auto
  moreover have "(\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))" 
  proof -
    {fix k
    assume kj:"k<j"
    then have "Suc k \<ge> length l \<or>  \<not> ( (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))) " using pj by auto
    then have "(\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))"
    proof
      {assume "length l \<le> Suc k" 
       thus ?thesis using kj pj by auto
      }
      {assume "\<not> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
       also have "k + 1 < length l" using kj pj by auto
       ultimately show ?thesis
         using a0 cptn_tran_ce_i step_ce_elim_cases by blast
      }
    qed
    } thus ?thesis by auto
  qed
  ultimately show ?thesis by auto
qed


lemma skip_com_all_skip:
assumes a0:"(\<Gamma>, l) \<in> cptn" and
        a1:"fst (l!i) = Skip" and
        a2:"i<length l" 
   shows "\<forall>j. j\<ge>i \<and> j <length l \<longrightarrow> fst (l!j) = Skip"
using a0 a1 a2
proof (induct "length l - (i + 1)" arbitrary: i)
  case 0  thus ?case by (metis Suc_eq_plus1 Suc_leI diff_is_0_eq nat_less_le zero_less_diff) 
next 
  case (Suc n)
  then have l:"Suc i < length l" by arith
  have n:"n = (length l) - (Suc i + 1)" using Suc by arith
  then have "\<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow>\<^sub>c\<^sub>e l ! Suc i" using cptn_tran_ce_i Suc
    by (metis (no_types) Suc.hyps(2) a0 cptn_tran_ce_i zero_less_Suc zero_less_diff)
  then have "\<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow> l ! Suc i \<or> \<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow>\<^sub>e l ! Suc i" 
    using step_ce_elim_cases by blast  
  then have or:"fst(l!Suc i) = Skip" 
  proof
    {assume "\<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow>\<^sub>e l ! Suc i" 
     thus ?thesis using Suc(4) by (metis env_c_c' prod.collapse)
    }
  next
   {assume step:"\<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow> l ! Suc i" 
     {assume "fst(l!i) = Skip" 
      then have ?thesis using step
        using SmallStepCon.final_def SmallStepCon.no_step_final' by blast
     }note left = this
     {assume "fst(l!i) = Throw"
      then have ?thesis using step stepc_elim_cases
      proof -
        have "\<exists>x. l ! Suc i = (LanguageCon.com.Skip, x)"
          by (metis (no_types) \<open>fst (l ! i) = LanguageCon.com.Throw\<close> local.step stepc_elim_cases(11) surjective_pairing)
        then show ?thesis
          by fastforce
      qed      
     } then show ?thesis using Suc(4) left by auto
    }
  qed
  show ?case using Suc(1)[OF n a0 or l] Suc(4) Suc(5) by (metis le_less_Suc_eq not_le) 
qed

lemma terminal_com_all_term:
assumes a0:"(\<Gamma>, l) \<in> cptn" and
        a1:"fst (l!i) = Skip \<or> fst (l!i) = Throw" and
        a2:"i<length l" 
   shows "\<forall>j. j\<ge>i \<and> j <length l \<longrightarrow> fst (l!j) = Skip \<or> fst (l!j) = Throw"
using a0 a1 a2
proof (induct "length l - (i + 1)" arbitrary: i)
  case 0  thus ?case by (metis Suc_eq_plus1 Suc_leI diff_is_0_eq nat_less_le zero_less_diff) 
next 
  case (Suc n)
  then have l:"Suc i < length l" by arith
  have n:"n = (length l) - (Suc i + 1)" using Suc by arith
  then have "\<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow>\<^sub>c\<^sub>e l ! Suc i" using cptn_tran_ce_i Suc
    by (metis (no_types) Suc.hyps(2) a0 cptn_tran_ce_i zero_less_Suc zero_less_diff)
  then have "\<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow> l ! Suc i \<or> \<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow>\<^sub>e l ! Suc i" 
    using step_ce_elim_cases by blast  
  then have or:"fst(l!Suc i) = Skip \<or> fst(l!Suc i) = Throw" 
  proof
    {assume "\<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow>\<^sub>e l ! Suc i" 
     thus ?thesis using Suc(4) by (metis env_c_c' prod.collapse)
    }
  next
   {assume step:"\<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow> l ! Suc i" 
     {assume "fst(l!i) = Skip" 
      then have ?thesis using step
        using SmallStepCon.final_def SmallStepCon.no_step_final' by blast
     }note left = this
     {assume "fst(l!i) = Throw"
      then have ?thesis using step stepc_elim_cases
      proof -
        have "\<exists>x. l ! Suc i = (LanguageCon.com.Skip, x)"
          by (metis (no_types) \<open>fst (l ! i) = LanguageCon.com.Throw\<close> local.step stepc_elim_cases(11) surjective_pairing)
        then show ?thesis
          by fastforce
      qed      
     } then show ?thesis using Suc(4) left by auto
    }
  qed
  show ?case using Suc(1)[OF n a0 or l] Suc(4) Suc(5) by (metis le_less_Suc_eq not_le) 
qed

lemma only_one_c_comp_tran:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!0) = c" and         
         a2: "Suc i<length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "i < j \<and> Suc j < length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<and> fst (l!j) = c" and
         a4: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c, s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> 
                        ((c1=Skip) \<or> (c1=Throw)) " and
         a5: "(\<forall>k < i. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
   shows "P"
proof - 
  have fst:"fst (l!i) = c" using a0 a1 a5
    by (simp add: a2 cptn_env_same_prog)
  then have suci:"fst (l!Suc i) = Skip \<or> fst (l!Suc i) = Throw" 
    using a4 by (metis a2 surjective_pairing) 
  then have "fst (l!j) = Skip \<or> fst (l!j) = Throw" 
  proof -
    have "Suc i \<le> j"
      using Suc_leI a3 by presburger
    then show ?thesis
      using Suc_lessD  terminal_com_all_term[OF a0 suci] a2 a3 by blast
  qed 
  thus ?thesis
  proof 
    {assume "fst (l ! j) = Skip"
     then show ?thesis using a3 SmallStepCon.final_def SmallStepCon.no_step_final' by blast
    }
  next
    {assume asm:"fst (l ! j) = Throw"
     then show ?thesis       
       proof (cases "snd (l!i)")
         case Normal 
         thus ?thesis using a3 a2 fst asm
           by (metis SmallStepCon.final_def SmallStepCon.no_step_final') 
       next
         case Abrupt thus ?thesis using a3 a2 fst asm skip_com_all_skip
             suci by (metis Suc_leI Suc_lessD a0 mod_env_not_component prod.collapse)
           
       next 
         case Fault thus ?thesis using a3 a2 fst asm skip_com_all_skip 
           suci by (metis Suc_leI Suc_lessD a0 mod_env_not_component prod.collapse)
       next 
         case Stuck thus ?thesis using a3 a2 fst asm skip_com_all_skip 
             suci by (metis Suc_leI Suc_lessD a0 mod_env_not_component prod.collapse)
       qed
    } 
  qed
qed

lemma only_one_component_tran1:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!0) = c" and         
         a2: "Suc i<length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "j \<noteq> i \<and> Suc j < length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<and> fst (l!j) = c" and
         a4: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c, s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> 
                        ((c1=Skip) \<or> (c1=Throw)) " and
         a5: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!0) \<in> Normal ` p \<and> 
                                        Sta q rely \<and> snd (l!Suc j) \<in> Normal ` q "
   shows "P"
proof (cases "j=i")
  case True thus ?thesis using a3 by auto
next
  case False note j_neq_i=this 
  thus ?thesis
  proof (cases "j<i")
    case True 
    thus ?thesis 
    proof -
      obtain bb :: "'b set \<Rightarrow> ('b \<Rightarrow> ('b, 'c) xstate) \<Rightarrow> ('b, 'c) xstate \<Rightarrow> 'b" where
        "\<forall>x0 x1 x2. (\<exists>v3. x2 = x1 v3 \<and> v3 \<in> x0) = (x2 = x1 (bb x0 x1 x2) \<and> bb x0 x1 x2 \<in> x0)"
        by moura
      then have f1: "\<forall>x f B. x \<notin> f ` B \<or> x = f (bb B f x) \<and> bb B f x \<in> B"
        by (meson imageE)
      then have "\<Gamma>\<turnstile>\<^sub>c (c, snd (l ! j)) \<rightarrow> (fst (l ! Suc j), Normal (bb q Normal (snd (l ! Suc j))))"
        by (metis (no_types) a3 a5 surjective_pairing)
      then show ?thesis
        using f1 by (meson Suc_leI a0 a2 a4 a5 True only_one_component_tran_j)
    qed  
  next
    case False 
    obtain j1 
    where all_ev:"j1\<le>i \<and>  
                 (\<Gamma>\<turnstile>\<^sub>c(l!j1)  \<rightarrow> (l!(Suc j1))) \<and> 
                 (\<forall>k < j1. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
      using a0 a2 a3 exist_first_comp_tran by blast
    then have fst:"fst (l!j1) = c" 
      using a0 a1 a2 cptn_env_same_prog le_imp_less_Suc less_trans_Suc by blast
    have suc:"Suc j1 < length l \<and> \<Gamma>\<turnstile>\<^sub>c l ! j1 \<rightarrow> l ! Suc j1" using all_ev a2
       using Suc_lessD le_eq_less_or_eq less_trans_Suc by linarith
    have evs:"(\<forall>k < j1. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))" using all_ev by auto
    have j:"j1 < j \<and> Suc j < length l \<and> \<Gamma>\<turnstile>\<^sub>c l ! j \<rightarrow> l ! Suc j \<and> fst (l ! j) = c"
      using a3 all_ev False by auto
    then show ?thesis 
      using only_one_c_comp_tran[OF a0 a1 suc j a4 evs] by auto   
  qed
qed  
 
lemma only_one_component_tran_i:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = c" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "k\<le>j \<and> j \<noteq> i \<and> Suc j < length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<and> fst (l!j) = c" and
         a4: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c, s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> 
                        ((c1=Skip) \<or> (c1=Throw)) " and
         a5: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!k) \<in> Normal ` p \<and> 
                                        Sta q rely \<and> snd (l!Suc j) \<in> Normal ` q "
   shows "P"
using a0 a1 a2 a3 a4 a5
proof (induct k arbitrary: l i j p q)
  case 0 show ?thesis using only_one_component_tran1[OF 0(1) 0(2) ]  0 by blast
next
  case (Suc n) 
   then obtain a1 l1 where l: "l=a1#l1"
    by (metis less_nat_zero_code list.exhaust list.size(3))
  then have l1notempty:"l1\<noteq>[]" using Suc by force    
  then obtain i' where i': "i=Suc i'" using Suc 
    using less_imp_Suc_add using Suc_le_D by meson 
  then obtain j' where j': "j=Suc j'" using Suc
    using Suc_le_D by meson      
  have a0:"(\<Gamma>,l1)\<in>cptn" using Suc l
    using tl_in_cptn l1notempty by meson
  moreover have a1:"fst (l1 ! n) = c"
    using Suc l l1notempty by force  
  moreover have a2:"Suc i' < length l1 \<and> n \<le> i' \<and> \<Gamma>\<turnstile>\<^sub>c l1 ! i' \<rightarrow> (l1 ! Suc i')"
    using Suc l l1notempty i' by auto
  moreover have a3:"n \<le> j' \<and> j' \<noteq> i' \<and> Suc j' < length l1 \<and> \<Gamma>\<turnstile>\<^sub>c l1 ! j' \<rightarrow> (l1 ! Suc j') \<and> fst (l1!j') = c"
    using Suc l l1notempty i' j' by auto
  moreover have a4:"env_tran_right \<Gamma> l1 rely \<and>
                  Sta p rely \<and> snd (l1!n) \<in> Normal ` p \<and> 
                  Sta q rely \<and> snd (l1 ! Suc j') \<in> Normal ` q " 
     using Suc(7) l j' unfolding env_tran_right_def by fastforce
  show ?case using Suc(1)[OF a0 a1 a2 a3 Suc(6) a4] by auto
qed

lemma only_one_component_tran:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = c" and         
         a2: "k\<le>i \<and>  i \<noteq> j \<and> Suc i<length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i))) \<and>   fst (l!i) = c" and
         a3: "k\<le>j \<and> Suc j < length l" and
         a4: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> 
                        ((c1=Skip) \<or> (c1=Throw))" and
         a5: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!k) \<in> Normal ` p \<and> 
                                        Sta q rely \<and> snd (l!Suc i) \<in> Normal ` q "
   shows "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
using a0 a1 a2 a3 a4 a5 only_one_component_tran_i
proof -
  {assume "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<or> (\<not> \<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"
   then have  "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
   proof
     assume "\<Gamma>\<turnstile>\<^sub>c l ! j \<rightarrow> (l ! Suc j)" 
       then have j:"Suc j<length l \<and> k\<le>j \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" using a3 by auto
       show ?thesis using only_one_component_tran_i[OF a0 a1 j a2 a4 a5] 
        by blast 
   next
      assume "\<not> \<Gamma>\<turnstile>\<^sub>c l ! j \<rightarrow> (l ! Suc j)"
        thus ?thesis
          by (metis Suc_eq_plus1 a0 a3 cptn_tran_ce_i step_ce_elim_cases)
   qed
  } thus ?thesis by auto
qed
  
lemma only_one_component_tran_all_env:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = c" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i))) \<and> fst (l!i) = c" and
         a3: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> 
                        ((c1=Skip) \<or> (c1=Throw))" and
         a4: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!k) \<in> Normal ` p \<and> 
                                        Sta q rely \<and> snd (l!Suc i) \<in> Normal ` q "
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof -
  {fix j
  assume ass:"k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l)"
  then have a2:"k \<le> i \<and> i \<noteq> j \<and> Suc i < length l \<and> \<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow> l ! Suc i \<and> fst (l ! i) = c"
    using a2 by auto
  then have "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))" 
    using only_one_component_tran[OF a0 a1 ] a2 a3 ass a4 by blast
  } thus ?thesis by auto
qed

lemma only_one_component_tran_all_not_comp:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = c" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i))) \<and> fst (l!i) = c" and
         a3: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c, s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> 
                        ((c1=Skip) \<or> (c1=Throw))" and
         a4: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!k) \<in> Normal ` p \<and> 
                                        Sta q rely \<and> snd (l!Suc i) \<in> Normal ` q "
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"
proof -
  {fix j
  assume ass:"k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l)"
  then have "\<not>(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"    
      using a0 a1 a2 a3 a4 only_one_component_tran_i ass by blast   
  } thus ?thesis by auto
qed

lemma final_exist_component_tran1:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
          a1: "fst (l!i) = c" and               
          a2: "env_tran \<Gamma> q l R \<and> Sta q R" and
          a3: "i\<le>j \<and> j < length l \<and> final (l!j)" and          
          a5: "c\<noteq>Skip \<and> c\<noteq>Throw"
  shows "\<exists>k. k\<ge>i \<and> k<j \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
proof -
  {assume "\<forall>k. k\<ge>i \<and>  k<j \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))" 
   then have "\<forall>k. k\<ge>i \<and>  k<j \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))"
   by (metis (no_types, lifting) Suc_eq_plus1 a0 a3 cptn_tran_ce_i less_trans_Suc step_ce_elim_cases)
   then have "fst (l!j) =  fst (l!i)" using cptn_i_env_same_prog a0 a3 by blast 
   then have False using a3 a1 a5 unfolding final_def by auto
  }  
  thus ?thesis by auto
qed  

lemma final_exist_component_tran:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
          a1: "fst (l!i) = c" and                         
          a2: "i\<le>j \<and> j < length l \<and> final (l!j)" and          
          a3: "c\<noteq>Skip \<and> c\<noteq>Throw"
  shows "\<exists>k. k\<ge>i \<and> k<j \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
proof -
  {assume "\<forall>k. k\<ge>i \<and>  k<j \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))" 
   then have "\<forall>k. k\<ge>i \<and>  k<j \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))"
   by (metis (no_types, lifting) Suc_eq_plus1 a0 a2 cptn_tran_ce_i less_trans_Suc step_ce_elim_cases)
   then have "fst (l!j) =  fst (l!i)" using cptn_i_env_same_prog a0 a2 by blast 
   then have False using a2 a1 a3 unfolding final_def by auto
  }  
  thus ?thesis by auto
qed

lemma suc_not_final_final_c_tran:
 assumes a0: "(\<Gamma>, l) \<in> cptn " and 
         a1: "Suc j< length l \<and> \<not>final (l!j) \<and> final (l!Suc j)"
 shows "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"
proof -
   obtain x xs where l:"l = x#xs" using a0 cptn.simps by blast
   obtain c1 s1 c2 s2 where l1:"l!j = (c1,s1) \<and> l!(Suc j) = (c2,s2)" using a1 by fastforce
   have "\<not> \<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j))" 
   proof -
      { assume a:"\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j))"
        then have eq_fst:"fst (l!j) = fst (l!Suc j)" by (metis env_c_c' prod.collapse)
        { assume "fst (l!Suc j) = Skip"
          then have "False" using a1 eq_fst unfolding final_def by fastforce
        }note p1=this
        { assume "fst (l!Suc j) = Throw \<and> (\<exists>s. snd (l!Suc j) = Normal s)" 
          then have "False" using a1 eq_fst unfolding final_def
          by (metis a eenv_normal_s'_normal_s local.l1 snd_conv)
        }
        then have False using a1 p1 unfolding final_def by fastforce
      } thus ?thesis by auto
   qed
   also have "\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>c\<^sub>e (l!(Suc j))" using l cptn_stepc_rtran a0 a1 by fastforce  
   ultimately show ?thesis using step_ce_not_step_e_step_c local.l1 by fastforce 
qed
 
lemma final_exist_component_tran_final:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and                                  
          a2: "i\<le>j \<and> j < length l \<and> final (l!j)" and                             
          a3: "\<not>final(l!i)" 
  shows "\<exists>k. k\<ge>i \<and> k<j \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))) \<and> final(l!(Suc k))"
proof -
  let ?P = "\<lambda>j. i\<le>j \<and> j < length l \<and> final (l!j)"
  obtain k where k:"?P k \<and> (\<forall>i<k. \<not> ?P i)" using a2 exists_first_occ[of ?P j] by auto
  then have i_k_not_final:"\<forall>i'<k. i'\<ge>i \<longrightarrow> \<not>final (l!i')" using a2 by fastforce
  have i_eq_j:"i<j" using a2 a3 using le_imp_less_or_eq by auto 
  then obtain pre_k  where pre_k:"Suc pre_k = k" using a2 k
    by (metis a3 eq_iff le0 lessE neq0_conv) 
  then have "\<Gamma>\<turnstile>\<^sub>c(l!pre_k)  \<rightarrow> (l!k)"
  proof -
    have "pre_k \<ge>i" using pre_k i_eq_j using a3 k le_Suc_eq by blast  
    then have "\<not>(final (l!pre_k))" using i_k_not_final pre_k by auto 
    thus ?thesis using suc_not_final_final_c_tran a0 a2 pre_k k by fastforce
  qed
  thus ?thesis using pre_k by (metis a2 a3 i_k_not_final k le_Suc_eq not_less_eq)
qed 


subsection {* Basic Sound *}

lemma basic_skip:
   "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Basic f e, s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> c1=Skip"
proof -
  {fix s1 s2 c1
   assume "\<Gamma>\<turnstile>\<^sub>c(Basic f e,s1)  \<rightarrow> ((c1,s2))"     
   then have "c1=Skip" using stepc_elim_cases(3) by blast    
  } thus ?thesis by auto 
qed  

lemma no_comp_tran_before_i_basic:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Basic f e" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "k\<le>j \<and> j < i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" and
         a4: "\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))" and  
         a5: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!0) \<in> Normal ` p \<and> 
                                        Sta q rely \<and> snd (l!Suc j) \<in> Normal ` q"        
   shows "P"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Basic f e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  basic_skip by fastforce                  
  thus ?thesis using  a0 a1 a2 a3 a4 a5 no_comp_tran_before_i by blast
qed

lemma only_one_component_tran_i_basic:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Basic f e" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "k\<le>j \<and> j \<noteq> i \<and> Suc j < length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<and> fst (l!j) =  Basic f e" and
         a4: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!k) \<in> Normal ` p \<and> 
                                        Sta q rely \<and> snd (l!Suc j) \<in> Normal ` q"     
   shows "P"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Basic f e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  basic_skip by blast
  thus ?thesis using  a0 a1 a2 a3 a4 only_one_component_tran_i[OF a0 a1 a2 ] by blast
qed   

lemma only_one_component_tran_basic:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Basic f e" and         
         a2: " k\<le>i \<and> i \<noteq> j \<and>  Suc i<length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i))) \<and> fst (l!i) = Basic f e" and
         a3: "k\<le>j  \<and> Suc j < length l" and
         a4: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!k) \<in> Normal ` p \<and> 
                                       Sta q rely \<and> snd (l!Suc i) \<in> Normal ` q"       
   shows "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Basic f e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  basic_skip by blast
  thus ?thesis using  a0 a1 a2 a3 a4 only_one_component_tran by blast
qed   

lemma only_one_component_tran_all_env_basic:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Basic f e" and         
         a2: "k\<le>i \<and> Suc i<length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i))) \<and> fst (l!i) = Basic f e" and        
         a3: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!k) \<in> Normal ` p \<and> 
                                       Sta q rely \<and> snd (l!Suc i) \<in> Normal ` q"
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof -
  have b: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Basic f e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  basic_skip by blast
  show ?thesis 
    by (metis (no_types) a0 a1 a2 a3 only_one_component_tran_basic) 
qed   

lemma only_one_component_tran_all_not_comp_basic:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Basic f e" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))  \<and> fst (l!i) = Basic f e" and         
         a3: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!k) \<in> Normal ` p \<and> 
                                       Sta q rely \<and> snd (l!Suc i) \<in> Normal ` q"     
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Basic f e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  basic_skip by blast
  thus ?thesis using  a0 a1 a2 a3 only_one_component_tran_all_not_comp by blast
qed   

lemma one_component_tran_basic:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!0) = Basic f e" and         
         a2: "Suc k<length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))" and
         a3: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!0) \<in> Normal ` p \<and> 
                                        Sta q rely" and
         a4:"p \<subseteq> {s. f s \<in> q}"
           
  shows "\<forall>j. 0\<le>j \<and> j\<noteq>k \<and> Suc j < (length l) \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Basic f e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  basic_skip by blast
  also obtain j where first:"(Suc j<length l \<and>  (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))) \<and> 
                 (\<forall>k < j. \<not>((\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))))"
    by (metis (no_types) a2 exist_first_comp_tran')
  moreover then have prg_j:"fst (l!j) = Basic f e"  using a1 a0
   by (metis cptn_env_same_prog not_step_comp_step_env)
  moreover have sta_j:"snd (l!j) \<in> Normal ` p"
  proof -
    have a0':"0\<le>j \<and> j<(length l)" using first by auto
    have a1':"(\<forall>k. 0\<le>k \<and> k < j \<longrightarrow> ((\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))))" 
      using first not_step_comp_step_env a0 by fastforce   
    thus ?thesis using stability first a3 a1'  a0' by blast 
  qed 
  then have "snd (l!Suc j) \<in> Normal ` q" using a4 first prg_j
  proof -
    obtain s where "snd (l!j) = Normal s \<and> s\<in>p" using sta_j by fastforce
    moreover then have "fst(l!Suc j) = Skip \<and> snd(l!Suc j) = Normal (f s)" using first
      by (metis fst_conv prg_j snd_conv stepc_Normal_elim_cases(3) surjective_pairing)
    ultimately show ?thesis using a4 by fastforce
  qed
  then have "\<forall>i. 0\<le>i \<and> i\<noteq>j \<and> Suc i < (length l) \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))"
    using only_one_component_tran_all_not_comp_basic[OF a0 a1] first a3 
          a0 a1 calculation(1) only_one_component_tran1 prg_j by blast 
  moreover then have "k=j" using a2 by fastforce
  ultimately show ?thesis by auto
qed   

lemma one_component_tran_basic_env:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!0) = Basic f e" and         
         a2: "Suc k<length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))" and
         a3: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!0) \<in> Normal ` p \<and> 
                                        Sta q rely" and
         a4:"p \<subseteq> {s. f s \<in> q}"           
  shows "\<forall>j. 0\<le>j \<and> j\<noteq>k \<and> Suc j < (length l) \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j))"
proof - 
  have "\<forall>j. 0\<le>j \<and> j\<noteq>k \<and> Suc j < (length l) \<longrightarrow> \<not> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"
  using one_component_tran_basic[OF a0 a1 a2 a3 a4] by auto
  thus ?thesis using  a0 
     by (metis Suc_eq_plus1 cptn_tran_ce_i step_ce_elim_cases)
qed

lemma final_exist_component_tran_basic:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
          a1: "fst (l!i) = Basic f e" and               
          a2: "env_tran \<Gamma> q l R" and
          a3: "i\<le>j \<and> j < length l \<and> final (l!j)" 
  shows "\<exists>k. k\<ge>i \<and> k<j \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
proof - 
  show ?thesis using  a0 a1 a2 a3 final_exist_component_tran by blast
qed   

(*lemma assumes a0:"\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  c sat [p, R, G, q,a]"
      shows "\<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub>  c sat [p, R, G, q,a]"
proof-
  {     
    assume a01:"\<forall>(b,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call b) sat [p, R, G, q,a]"
    have "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [p, R, G, q,a]"
    proof-
      {fix s l
        assume a02:"(\<Gamma>,l)\<in>cpn n \<Gamma> c s" and
               a03:"(\<Gamma>,l)\<in>assum(p, R)"
        have "(\<Gamma>,l)\<in>comm(G, (q,a)) F"  
        proof-
          have cpn_cp:"(\<Gamma>,l)\<in>cp \<Gamma> c s" using a02
            using cp_def cpn_def cptn_if_cptn_mod cptn_mod_nest_cptn_mod by fastforce
        qed
      } then show ?thesis unfolding  com_validityn_def cpn_def by auto
    qed
  } then show ?thesis unfolding com_cvalidityn_def by auto
qed *)

lemma Basic_sound1: 
  assumes a0:"p \<subseteq> {s. f s \<in> q}" and
      a1:"(\<forall>s t. s\<in>p \<and> (t=f s) \<longrightarrow> (Normal s,Normal t) \<in> G)" and
      a2:"Sta p R" and
      a3:"Sta q R" and
      a10:"c \<in> cp \<Gamma> (Basic f e) s" and a11:"c \<in> assum(p, R)"
    shows "c\<in>comm(G, (q,a)) F"
proof -   
  obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
   have cp:"l!0=(Basic f e,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
   have assum:"snd(l!0) \<in> Normal ` (p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
             (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
               (snd(l!i), snd(l!(Suc i))) \<in> R)" 
   using a11 c_prod unfolding assum_def by simp
   have concl:"(\<forall>i ns ns'. Suc i<length l \<longrightarrow> 
           \<Gamma>1\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow>                             
           (snd(l!i), snd(l!(Suc i))) \<in> G)"
   proof -
   { fix k
     assume a00:"Suc k<length l" and
            a11:"\<Gamma>1\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))"                
     have len_l:"length l > 0" using cp using cptn.simps by blast 
     then obtain a l1 where l:"l=a#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
     have last_l:"last l = l!(length l-1)"
       using last_length [of a l1] l by fastforce
     have env_tran:"env_tran \<Gamma> p l R" using assum env_tran_def cp by blast
     then have env_tran_right: "env_tran_right \<Gamma> l R" 
       using env_tran env_tran_right_def a2 unfolding env_tran_def by auto
     then have all_event:"\<forall>j. 0\<le>j \<and> j \<noteq> k \<and> Suc j < length l \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
       using one_component_tran_basic_env[of \<Gamma> l f e k R] a0 a00 a11 a2 a3 assum cp 
             env_tran_right fst_conv
       by metis
     then have before_k_all_evn:"\<forall>j. 0\<le>j \<and> j < k  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
           using a00 a11  by fastforce
     then have k_basic:"fst(l!k) = Basic f e \<and> snd (l!k) \<in> Normal ` (p)" 
       using  cp env_tran_right a2 assum a00 a11  stability[of p R l 0 k k \<Gamma>]
       by force
     have suc_k_skip_q:"fst(l!Suc k) = Skip \<and> snd (l!(Suc k)) \<in> Normal ` q"
     proof 
       show suc_skip: "fst(l!Suc k) = Skip"
         using a0 a00 a11  k_basic by (metis basic_skip surjective_pairing) 
     next
       obtain s' where k_s: "snd (l!k)=Normal s' \<and> s' \<in> (p)" 
         using a00 a11  k_basic by auto
       then have "snd (l!(Suc k)) = Normal (f s')"          
         using a00 a11  k_basic stepc_Normal_elim_cases(3)
         by (metis prod.inject surjective_pairing)          
       then show "snd (l!(Suc k)) \<in> Normal ` q" using a0 k_s by blast
     qed
     obtain s' s'' where 
        ss:"snd (l!k) = Normal s' \<and> s' \<in> (p) \<and>  
           snd (l!(Suc k)) = Normal s'' \<and> s'' \<in> q"
       using suc_k_skip_q k_basic by fastforce         
     then have "(snd(l!k), snd(l!(Suc k))) \<in>  G"
       using a0 a1 a2
       by (metis Pair_inject a11 k_basic prod.exhaust_sel stepc_Normal_elim_cases(3))
   } thus ?thesis by auto qed
   have concr:"(final (last l)  \<longrightarrow> 
               snd (last l) \<notin> Fault ` F  \<longrightarrow>
               ((fst (last l) = Skip \<and> 
                snd (last l) \<in> Normal ` q)) \<or>
                (fst (last l) = Throw \<and> 
                snd (last l) \<in> Normal ` (a)))"
   proof-
   { 
     assume valid:"final (last l)"
     have len_l:"length l > 0" using cp using cptn.simps by blast 
     then obtain a l1 where l:"l=a#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
     have last_l:"last l = l!(length l-1)"
       using last_length [of a l1] l by fastforce
     have env_tran:"env_tran \<Gamma> p l R" using assum env_tran_def cp by blast
     then have env_tran_right: "env_tran_right \<Gamma> l R" 
       using env_tran env_tran_right_def a2 unfolding env_tran_def by auto
     have "\<exists>k. k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
     proof -             
       have "0\<le> (length l-1)" using len_l last_l by auto
       moreover have "(length l-1) < length l" using len_l by auto
       moreover have "final (l!(length l-1))" using valid last_l by auto
       moreover have "fst (l!0) = Basic f e" using cp by auto
       ultimately show ?thesis 
         using cp final_exist_component_tran_basic env_tran a2 by blast 
     qed
     then obtain k where k_comp_tran: "k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
       by auto
     moreover then have "Suc k < length l" by auto
     ultimately have all_event:"\<forall>j. 0\<le>j \<and> j \<noteq> k \<and> Suc j < length l \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
        using one_component_tran_basic_env[of \<Gamma> l f e k R] a0  a11 a2 a3 assum cp 
             env_tran_right fst_conv by metis           
     then have before_k_all_evn:"\<forall>j. 0\<le>j \<and> j < k  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
           using k_comp_tran by fastforce
     then have k_basic:"fst(l!k) = Basic f e \<and> snd (l!k) \<in> Normal ` (p)" 
       using  cp env_tran_right a2 assum k_comp_tran stability[of p R l 0 k k \<Gamma>]
       by force
     have suc_k_skip_q:"fst(l!Suc k) = Skip \<and> snd (l!(Suc k)) \<in> Normal ` q"
     proof 
       show suc_skip: "fst(l!Suc k) = Skip"
         using a0 k_comp_tran k_basic by (metis basic_skip surjective_pairing) 
     next
       obtain s' where k_s: "snd (l!k)=Normal s' \<and> s' \<in> (p)" 
         using k_comp_tran k_basic by auto
       then have "snd (l!(Suc k)) = Normal (f s')"          
         using k_comp_tran k_basic stepc_Normal_elim_cases(3)
         by (metis prod.inject surjective_pairing)          
       then show "snd (l!(Suc k)) \<in> Normal ` q" using a0 using k_s by blast
     qed
     have after_k_all_evn:"\<forall>j. (Suc k)\<le>j \<and> Suc j < (length l)  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
           using all_event k_comp_tran by fastforce                            
     then have fst_last_skip:"fst (last l) = Skip \<and> 
                         snd ((last l)) \<in> Normal ` q"
     using  a2 last_l len_l cp env_tran_right a3 suc_k_skip_q assum k_comp_tran 
            stability [of q R l "Suc k" "((length l) - 1)" _ \<Gamma>] 
       by fastforce                 
   } thus ?thesis by auto qed
   note res = conjI [OF concl concr]                               
   thus ?thesis using c_prod unfolding comm_def by auto 
 qed


lemma Basic_sound: 
       "p \<subseteq> {s. f s \<in> q} \<Longrightarrow>
      (\<forall>s t. s\<in>p \<and> (t=f s) \<longrightarrow> (Normal s,Normal t) \<in> G) \<Longrightarrow>       
       Sta p R \<Longrightarrow>
       Sta q R \<Longrightarrow>       
       \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub>  (Basic f e) sat [p, R, G, q,a]"
proof -  
 assume
    a0:"p \<subseteq> {s. f s \<in> q}" and
    a1:"(\<forall>s t. s\<in>p \<and> (t=f s) \<longrightarrow> (Normal s,Normal t) \<in> G)" and
    a2:"Sta p R " and
    a3:"Sta q R" 
{
    fix s
    have "cpn n \<Gamma> (Basic f e) s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cpn n \<Gamma> (Basic f e) s" and a11:"c \<in> assum(p, R)"
      then have a10:"c\<in>cp \<Gamma> (Basic f e) s"
        using cp_def cpn_def cptn_if_cptn_mod cptn_mod_nest_cptn_mod by blast
      have "c\<in>comm(G, (q,a)) F" using Basic_sound1[OF a0 a1 a2 a3 a10 a11] by auto      
    } thus ?thesis by auto
    qed 
  } 
  thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed

subsection {* Spec Sound *}

lemma spec_skip:
   "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> c1=Skip"
proof -
  {fix s1 s2 c1
   assume "\<Gamma>\<turnstile>\<^sub>c(Spec r e,s1)  \<rightarrow> ((c1,s2))"     
   then have "c1=Skip" using stepc_elim_cases(4) by force    
  } thus ?thesis by auto 
qed  


lemma no_comp_tran_before_i_spec:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Spec r e" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "k\<le>j \<and> j < i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" and
         a4: "\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))" and
         a5: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!0) \<in> Normal ` p \<and> 
                                        Sta q rely \<and> snd (l!Suc j) \<in> Normal ` q" 
   shows "P"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  spec_skip by blast
  thus ?thesis using  a0 a1 a2 a3 a4 a5 no_comp_tran_before_i by blast
qed

lemma only_one_component_tran_i_spec:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Spec r e" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "k\<le>j \<and> j \<noteq> i \<and> Suc j < length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<and> fst (l!j) =  Spec r e" and
         a4: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!k) \<in> Normal ` p \<and> 
                                        Sta q rely \<and> snd (l!Suc j) \<in> Normal ` q"     
   shows "P"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  spec_skip by blast
  thus ?thesis using  a0 a1 a2 a3 a4 only_one_component_tran_i[OF a0 a1 a2 ] by blast
qed   

lemma only_one_component_tran_spec:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Spec r e" and         
         a2: "k\<le>i  \<and> i \<noteq> j \<and> Suc i<length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i))) \<and> fst (l!i) =  Spec r e" and
         a3: "k\<le>j  \<and> Suc j < length l" and
         a4: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!k) \<in> Normal ` p \<and> 
                                        Sta q rely \<and> snd (l!Suc i) \<in> Normal ` q"       
   shows "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  spec_skip by blast
  thus ?thesis using  a0 a1 a2 a3 a4 only_one_component_tran by blast
qed   

lemma only_one_component_tran_all_env_spec:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Spec r e" and         
         a2: "k\<le>i \<and> Suc i<length l \<and>(\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))  \<and> fst (l!i) =  Spec r e" and         
         a3: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!k) \<in> Normal ` p \<and> 
                                        Sta q rely \<and> snd (l!Suc i) \<in> Normal ` q"       
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  spec_skip by blast
  thus ?thesis by (metis (no_types) a0 a1 a2 a3 only_one_component_tran_spec) 
qed   

lemma only_one_component_tran_all_not_comp_spec:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Spec r e" and         
         a2: "k\<le>i \<and> Suc i<length l \<and>(\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))  \<and> fst (l!i) =  Spec r e" and         
         a3: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!k) \<in> Normal ` p \<and> 
                                        Sta q rely \<and> snd (l!Suc i) \<in> Normal ` q"       
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  spec_skip by blast
  thus ?thesis using  a0 a1 a2 a3 only_one_component_tran_all_not_comp by blast
qed   

lemma one_component_tran_spec:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!0) = Spec r e" and         
         a2: "Suc k<length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))" and
         a3: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!0) \<in> Normal ` p \<and> 
                                        Sta q rely" and
         a4:"p \<subseteq> {s. (\<forall>t. (s,t)\<in>r \<longrightarrow> t \<in> q) \<and> (\<exists>t. (s,t) \<in> r)}"
           
  shows "\<forall>j. 0\<le>j \<and> j\<noteq>k \<and> Suc j < (length l) \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  spec_skip by blast
  also obtain j where first:"(Suc j<length l \<and>  (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!Suc j))) \<and> 
                 (\<forall>k < j. \<not>((\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))))"
    by (metis (no_types) a2 exist_first_comp_tran')
  moreover then have prg_j:"fst (l!j) = Spec r e" using a1 a0
   by (metis cptn_env_same_prog not_step_comp_step_env)
  moreover have sta_j:"snd (l!j) \<in> Normal ` p"
  proof -
    have a0':"0\<le>j \<and> j<(length l)" using first by auto
    have a1':"(\<forall>k. 0\<le>k \<and> k < j \<longrightarrow> ((\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))))" 
      using first not_step_comp_step_env a0 by fastforce   
    thus ?thesis using stability first a3 a1'  a0' by blast 
  qed 
  then have "snd (l!Suc j) \<in> Normal ` q" using a4 first prg_j
  proof -
    obtain s where s:"snd (l!j) = Normal s \<and> s\<in>p" using sta_j by fastforce       
    then have suc_skip: "fst (l!Suc j) = Skip"
      using spec_skip first prg_j a4 by (metis (no_types, lifting) prod.collapse)
    moreover obtain s' where  "snd (l!Suc j) = Normal s' \<and> (s,s')\<in>r" 
      proof -
      { have f1:"(\<Gamma>\<turnstile>\<^sub>c(fst(l!j),snd(l!j))  \<rightarrow> (fst(l!Suc j),snd(l!Suc j)))" using first by auto
        obtain t where "snd (l!Suc j) = Normal t"
        using step_spec_skip_normal_normal[of \<Gamma> "fst(l!j)" "snd(l!j)" "fst(l!Suc j)" "snd(l!Suc j)" r] 
         suc_skip prg_j s a4 f1 by blast
        moreover then have "(s,t)\<in>r" using a4 s prg_j f1 suc_skip stepc_Normal_elim_cases(4)
          by (metis (no_types, lifting)  stepc_Normal_elim_cases(4) prod.inject xstate.distinct(5) xstate.inject(1))
        ultimately have "\<exists>t. snd (l!Suc j)= Normal t  \<and> (s,t)\<in>r" by auto
      }
      then show "(\<And>s'. snd (l ! Suc j) = Normal s' \<and> (s, s') \<in> r \<Longrightarrow> thesis) \<Longrightarrow> thesis" ..
    qed             
    then show ?thesis using a4 sta_j s by auto
  qed
  then have "\<forall>i. 0\<le>i \<and> i\<noteq>j \<and> Suc i < (length l) \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))"
    using only_one_component_tran_all_not_comp_spec[OF a0 a1] first a3 
          a0 a1 calculation(1) only_one_component_tran1 prg_j by blast
  moreover then have "k=j" using a2 by fastforce
  ultimately show ?thesis by auto
qed   

lemma one_component_tran_spec_env:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!0) = Spec r e" and         
         a2: "Suc k<length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))" and
         a3: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!0) \<in> Normal ` p \<and> 
                                        Sta q rely" and
         a4:"p \<subseteq> {s. (\<forall>t. (s,t)\<in>r \<longrightarrow> t \<in> q) \<and> (\<exists>t. (s,t) \<in> r)}"           
  shows "\<forall>j. 0\<le>j \<and> j\<noteq>k \<and> Suc j < (length l) \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j))"
proof - 
  have "\<forall>j. 0\<le>j \<and> j\<noteq>k \<and> Suc j < (length l) \<longrightarrow> \<not> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"
  using one_component_tran_spec[OF a0 a1 a2 a3 a4] by auto
  thus ?thesis using  a0 
     by (metis Suc_eq_plus1 cptn_tran_ce_i step_ce_elim_cases)
qed

lemma final_exist_component_tran_spec:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
          a1: "fst (l!i) = Spec r e" and               
          a2: "env_tran \<Gamma> q l R " and
          a3: "i\<le>j \<and> j < length l \<and> final (l!j)" 
  shows "\<exists>k. k\<ge>i \<and> k<j \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  spec_skip by blast
  thus ?thesis using  a0 a1 a2 a3 final_exist_component_tran by blast
qed   
lemma Spec_sound1: 
       "p \<subseteq> {s. (\<forall>t. (s,t)\<in>r \<longrightarrow> t \<in> q) \<and> (\<exists>t. (s,t) \<in> r)} \<Longrightarrow>
       (\<forall>s t. s\<in>p  \<and> (s,t)\<in>r \<longrightarrow> (Normal s, Normal t) \<in> G) \<Longrightarrow>       
       Sta p R \<Longrightarrow>
       Sta q R \<Longrightarrow> 
       c \<in> cp \<Gamma> (Spec r e) s \<Longrightarrow>
       c \<in> assum(p, R) \<Longrightarrow>
       c \<in> comm (G, (q,a)) F"   
proof -  
 assume
  a0:"p \<subseteq> {s. (\<forall>t. (s,t)\<in>r \<longrightarrow> t \<in> q) \<and> (\<exists>t. (s,t) \<in> r)}" and
  a1:"(\<forall>s t. s\<in>p  \<and> (s,t)\<in>r \<longrightarrow> (Normal s,Normal t) \<in> G)" and
  a2:"Sta p R" and
  a3:"Sta q R" and 
  a10:"c \<in> cp \<Gamma> (Spec r e) s" and
  a11:"c \<in> assum(p, R)"

  obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
  have cp:"l!0=(Spec r e,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
   have assum:"snd(l!0) \<in> Normal ` (p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
             (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
               (snd(l!i), snd(l!(Suc i))) \<in> R)" 
   using a11 c_prod unfolding assum_def by simp
   have concl:"(\<forall>i ns ns'. Suc i<length l \<longrightarrow> 
           \<Gamma>1\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow>                                       
             (snd(l!i), snd(l!(Suc i))) \<in> G)"
   proof -
   { fix k
     assume a00:"Suc k<length l" and
            a11:"\<Gamma>1\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))"                
     obtain ck sk csk ssk where tran_pair:
       "\<Gamma>1\<turnstile>\<^sub>c (ck,sk)  \<rightarrow> (csk, ssk) \<and> (ck = fst (l!k)) \<and> (sk = snd (l!k)) \<and> (csk = fst (l!(Suc k))) \<and> (ssk = snd (l!(Suc k)))" 
       using a11 by fastforce
     have len_l:"length l > 0" using cp using cptn.simps by blast 
     then obtain a l1 where l:"l=a#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
     have last_l:"last l = l!(length l-1)"
       using last_length [of a l1] l by fastforce
     have env_tran:"env_tran \<Gamma> p l R" using assum env_tran_def cp by blast
     then have env_tran_right: "env_tran_right \<Gamma> l R" 
       using env_tran env_tran_right_def unfolding env_tran_def by auto
     then have all_event:"\<forall>j. 0\<le>j \<and> j \<noteq> k \<and> Suc j < length l \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
       using a00 a11   one_component_tran_spec_env[of \<Gamma> l r e k R] 
             env_tran_right fst_conv a0 a2 a3 cp len_l assum
       by fastforce
     then have before_k_all_evn:"\<forall>j. 0\<le>j \<and> j < k  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
           using a00 a11  by fastforce
     then have k_basic:"ck = Spec r e \<and> sk \<in> Normal ` (p)" 
       using  cp  env_tran_right a2 assum a00 a11 stability[of p R l 0 k k \<Gamma>] tran_pair
       by force
     have suc_skip: "csk = Skip"
        using a0 a00 k_basic tran_pair spec_skip by blast
     obtain s' where ss:"sk = Normal s' \<and> s' \<in> (p)" 
       using k_basic by fastforce
     obtain s'' where suc_k_skip_q:"ssk = Normal s'' \<and> (s',s'')\<in>r "           
     proof -                    
       {from ss  obtain t where "ssk = Normal t" 
         using step_spec_skip_normal_normal[of \<Gamma>1 ck sk csk ssk r e s'] 
               k_basic tran_pair a0 suc_skip
         by blast                      
       moreover then have "(s',t)\<in>r" using a0 k_basic ss a11 suc_skip 
         by (metis (no_types, lifting)  stepc_Normal_elim_cases(4) tran_pair prod.inject xstate.distinct(5) xstate.inject(1))            
       ultimately have "\<exists>t. ssk= Normal t  \<and> (s',t)\<in>r" by auto
       } 
     then show "(\<And>s''. ssk = Normal s''  \<and> (s',s'')\<in>r\<Longrightarrow> thesis) \<Longrightarrow> thesis" ..
     qed                                                                        
     then have "(snd(l!k), snd(l!(Suc k))) \<in> G"
       using ss a1 tran_pair   by force
   } thus ?thesis by auto qed
   have concr:"(final (last l)  \<longrightarrow> ((fst (last l) = Skip \<and> 
                                              snd (last l) \<in> Normal ` q)) \<or>
                                              (fst (last l) = Throw \<and> 
                                              snd (last l) \<in> Normal ` (a)))"
   proof-
   { 
     assume valid:"final (last l)"
     have len_l:"length l > 0" using cp using cptn.simps by blast 
     then obtain a l1 where l:"l=a#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
     have last_l:"last l = l!(length l-1)"
       using last_length [of a l1] l by fastforce
     have env_tran:"env_tran \<Gamma> p l R" using assum env_tran_def cp by blast
     then have env_tran_right: "env_tran_right \<Gamma> l R" 
       using env_tran env_tran_right_def unfolding env_tran_def by auto
     have "\<exists>k. k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
     proof -             
       have "0\<le> (length l-1)" using len_l last_l by auto
       moreover have "(length l-1) < length l" using len_l by auto
       moreover have "final (l!(length l-1))" using valid last_l by auto
       moreover have "fst (l!0) = Spec r e" using cp by auto
       ultimately show ?thesis 
         using cp final_exist_component_tran_spec env_tran  by blast 
     qed
     then obtain k  where k_comp_tran: "k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
       by auto
     then obtain ck sk csk ssk where tran_pair:
       "\<Gamma>1\<turnstile>\<^sub>c (ck,sk)  \<rightarrow> (csk, ssk) \<and> (ck = fst (l!k)) \<and> (sk = snd (l!k)) \<and> (csk = fst (l!(Suc k))) \<and> (ssk = snd (l!(Suc k)))" 
       using cp by fastforce
     moreover then have "Suc k < length l" using k_comp_tran by auto
     ultimately have all_event:"\<forall>j. 0\<le>j \<and> j \<noteq> k \<and> Suc j < length l \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
       using one_component_tran_spec_env[of \<Gamma> l r e k R] a0  a11 a2 a3 assum cp 
             env_tran_right fst_conv            
       by fastforce
     then have before_k_all_evn:"\<forall>j. 0\<le>j \<and> j < k  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
           using k_comp_tran by fastforce
     then have k_basic:"ck = Spec r e \<and> sk \<in> Normal ` (p)" 
       using cp env_tran_right a2 assum tran_pair k_comp_tran stability[of p R l 0 k k \<Gamma>] tran_pair
       by force
     have suc_skip: "csk = Skip"
        using a0  k_basic tran_pair spec_skip by blast
     have suc_k_skip_q:"ssk \<in> Normal ` q"           
     proof -         
       obtain s' where k_s: "sk =Normal s' \<and> s' \<in> (p)" 
         using k_basic by auto
       then obtain t where "ssk = Normal t" 
       using step_spec_skip_normal_normal[of \<Gamma>1 ck sk csk ssk r] k_basic tran_pair a0 suc_skip
       by blast           
       then obtain t where "ssk= Normal t" by fastforce
       then have "(s',t)\<in>r" using  k_basic k_s a11 suc_skip 
         by (metis (no_types, lifting)  stepc_Normal_elim_cases(4) tran_pair prod.inject xstate.distinct(5) xstate.inject(1))
       thus "ssk \<in> Normal ` q"  using a0 k_s `ssk = Normal t` by blast 
     qed    
     have after_k_all_evn:"\<forall>j. (Suc k)\<le>j \<and> Suc j < (length l)  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
           using all_event k_comp_tran by fastforce                            
     then have fst_last_skip:"fst (last l) = Skip \<and> 
                         snd ((last l)) \<in> Normal ` q"
     using l tran_pair suc_skip last_l len_l cp 
           env_tran_right a3 suc_k_skip_q 
           assum k_comp_tran stability [of q R l "Suc k" "((length l) - 1)" _ \<Gamma>] 
     by (metis One_nat_def Suc_eq_plus1 Suc_leI Suc_mono diff_Suc_1 lessI list.size(4))                  
   } thus ?thesis by auto qed
   note res = conjI [OF concl concr]                           
   thus ?thesis using c_prod unfolding comm_def by auto 
 qed
 
lemma Spec_sound: 
       "p \<subseteq> {s. (\<forall>t. (s,t)\<in>r \<longrightarrow> t \<in> q) \<and> (\<exists>t. (s,t) \<in> r)} \<Longrightarrow>
       (\<forall>s t. s\<in>p  \<and> (s,t)\<in>r \<longrightarrow> (Normal s, Normal t) \<in> G) \<Longrightarrow>       
       Sta p R \<Longrightarrow>
       Sta q R \<Longrightarrow>    
       \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub>  (Spec r e) sat [p, R, G, q,a]"
proof -  
 assume
    a0:"p \<subseteq> {s. (\<forall>t. (s,t)\<in>r \<longrightarrow> t \<in> q) \<and> (\<exists>t. (s,t) \<in> r)}" and
    a1:"(\<forall>s t. s\<in>p  \<and> (s,t)\<in>r \<longrightarrow> (Normal s,Normal t) \<in> G)" and
    a2:"Sta p R" and
    a3:"Sta q R" 
{
    fix s
    have "cpn n \<Gamma> (Spec r e) s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cpn n \<Gamma> (Spec r e) s" and a11:"c \<in> assum(p, R)"
      then have a10:"c\<in>cp \<Gamma> (Spec r e) s"
        using cp_def cpn_def cptn_if_cptn_mod cptn_mod_nest_cptn_mod by blast
      have "c\<in>comm(G, (q,a)) F" using Spec_sound1[OF a0 a1 a2 a3 a10 a11] by auto      
    } thus ?thesis by auto
    qed 
  } 
  thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed

subsection {* Await Sound *}

lemma await_skip:
   "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> c1=Skip \<or> (c1 = Throw \<and> (\<exists>s21. s2 =Normal s21 ))"
proof -
  {fix s1 s2 c1
   assume "\<Gamma>\<turnstile>\<^sub>c(Await b c e,s1)  \<rightarrow> ((c1,s2))"     
   then have "c1=Skip \<or>  (c1 = Throw \<and> (\<exists>s21. s2 =Normal s21 ))" using stepc_elim_cases(8) by blast    
  } thus ?thesis by auto 
qed  

lemma no_comp_tran_before_i_await:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Await b c e" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "k\<le>j \<and> j < i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" and
         a4: "\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))" and
         a5: "env_tran_right \<Gamma> l rely  \<and> Sta p rely \<and> snd (l!0) \<in> Normal ` p \<and> 
                                         Sta q rely \<and> snd (l!Suc j) \<in> Normal ` q"
   shows "P"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow>  c1=Skip \<or> (c1 = Throw \<and> (\<exists>s21. s2 =Normal s21 ))" 
    using  await_skip by blast
  thus ?thesis using  a0 a1 a2 a3 a4 a5 no_comp_tran_before_i by blast
qed

lemma only_one_component_tran_i_await:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Await b c e" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "k\<le>j \<and> j \<noteq> i \<and> Suc j < length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<and> fst (l!j) = Await b c e" and
         a4: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!k) \<in> Normal ` p \<and> 
                                        Sta q rely \<and> snd (l!Suc j) \<in> Normal ` q" 
   shows "P"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)\<or>(c1 = Throw \<and> (\<exists>s21. s2 =Normal s21 ))" 
    using  await_skip by blast
  thus ?thesis using  a0 a1 a2 a3 a4 only_one_component_tran_i by blast
qed   

lemma only_one_component_tran_await:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Await b c e" and         
         a2: " k\<le>i \<and> i \<noteq> j \<and>  Suc i<length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i))) \<and> fst (l!i) = Await b c e" and
         a3: "k\<le>j  \<and> Suc j < length l" and
         a4: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!k) \<in> Normal ` p \<and> 
                                       Sta q rely \<and> snd (l!Suc i) \<in> Normal ` q"     
   shows "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)\<or>(c1 = Throw \<and> (\<exists>s21. s2 =Normal s21 ))" 
    using  await_skip by blast
  thus ?thesis using  a0 a1 a2 a3 a4 only_one_component_tran by blast
qed   

lemma only_one_component_tran_all_env_await:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Await b c e" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))  \<and> fst (l!i) = Await b c e" and         
         a3: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!k) \<in> Normal ` p \<and> 
                                       Sta q rely \<and> snd (l!Suc i) \<in> Normal ` q"       
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof -
  have  a:"\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)\<or>(c1 = Throw)" 
    using  await_skip by blast
  thus ?thesis by (metis (no_types) a0 a1 a2 a3 only_one_component_tran_await)
qed
   

lemma only_one_component_tran_all_not_comp_await:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Await b c e" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))  \<and> fst (l!i) = Await b c e" and         
         a3: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!k) \<in> Normal ` p \<and> 
                                       Sta q rely \<and> snd (l!Suc i) \<in> Normal ` q" 
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)\<or>(c1 = Throw \<and> (\<exists>s21. s2 =Normal s21 ))" 
    using  await_skip by blast
  thus ?thesis using  a0 a1 a2 a3 only_one_component_tran_all_not_comp by blast
qed   

lemma one_component_tran_await:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!0) = Await b c e" and         
         a2: "Suc k<length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))" and
         a3: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!0) \<in> Normal ` p \<and> 
                                        Sta q rely \<and>
                                        Sta a rely" and
         a4:"\<forall>V. \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
             (p \<inter> b \<inter> {V}) c
             ({s. (Normal V, Normal s) \<in> G} \<inter> q),
             ({s. (Normal V, Normal s) \<in> G} \<inter> a)" and
         a5:"snd (last l) \<notin> Fault ` F"
           
  shows "(\<forall>j. 0\<le>j \<and> j\<noteq>k \<and> Suc j < (length l) \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))) \<and>
         (\<exists>s s'. fst (l!k) = Await b c e \<and> snd (l!k) \<in> Normal ` (p) \<and> snd (l!k) = Normal s \<and> snd (l!Suc k) = Normal s' \<and> 
            (snd (l!Suc k) \<in> Normal ` ({s'. (Normal s, Normal s') \<in> G} \<inter> q) \<or> 
             snd (l!Suc k) \<in> Normal ` ({s'. (Normal s, Normal s') \<in> G} \<inter> a)))"
proof -
  have  suc_skip:"\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)\<or> (c1=Throw \<and> (\<exists>s21. s2 =Normal s21 ))" 
    using  await_skip by blast
  also obtain j where first:"(Suc j<length l \<and>  (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))) \<and> 
                 (\<forall>k < j. \<not>((\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))))"
    by (metis (no_types) a2 exist_first_comp_tran')
  moreover then have prg_j:"fst (l!j) = Await b c e" using a1 a0
   by (metis cptn_env_same_prog not_step_comp_step_env)
  moreover have sta_j:"snd (l!j) \<in> Normal ` p"
  proof -
    have a0':"0\<le>j \<and> j<(length l)" using first by auto
    have a1':"(\<forall>k. 0\<le>k \<and> k < j \<longrightarrow> ((\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))))" 
      using first not_step_comp_step_env a0 by fastforce   
    thus ?thesis using stability first a3 a1'  a0' by blast 
  qed 
  from sta_j obtain s where 
      k_basic:"fst (l!j) = Await b c e \<and> snd (l!j) = Normal s \<and>  s \<in> p \<and> snd(l!j) \<in> Normal ` p" 
      using sta_j prg_j by fastforce
  then have conc:"snd (l!Suc j) \<in> Normal ` ({s'. (Normal s, Normal s') \<in> G} \<inter> q) \<or> 
             snd (l!Suc j) \<in> Normal ` ({s'. (Normal s, Normal s') \<in> G} \<inter> a)" 
  proof -    
    have "\<Gamma>\<^sub>\<not>\<^sub>a,{}\<Turnstile>\<^bsub>/F\<^esub> 
                     (p \<inter> b \<inter> {s}) c 
                     ({s'. (Normal s, Normal s') \<in> G} \<inter> q),
                     ({s'. (Normal s, Normal s') \<in> G} \<inter> a)"
      using  a4 hoare_sound by fastforce
    then have e_auto:"\<Gamma>\<^sub>\<not>\<^sub>a\<Turnstile>\<^bsub>/F\<^esub> (p \<inter> b \<inter> {s}) c 
                     ({s'. (Normal s, Normal s') \<in> G} \<inter> q),
                     ({s'. (Normal s, Normal s') \<in> G} \<inter> a)" 
      unfolding cvalid_def by auto    
    have f': "\<Gamma>\<turnstile>\<^sub>c(fst (l!j), snd(l!j))  \<rightarrow> (fst(l!(Suc j)), snd(l!(Suc j)))"      
      using first by auto
    have step_await:"Suc j<length l \<and> \<Gamma>\<turnstile>\<^sub>c (Await b c e,snd(l!j))  \<rightarrow> (fst(l!(Suc j)), snd(l!(Suc j)))"
             using f' k_basic first by fastforce           
    then have s'_in_bp:"s\<in> b \<and> s \<in> p"  using k_basic stepc_Normal_elim_cases(8) by metis
    then have "s \<in> (p \<inter> b)"  by fastforce
    moreover have test:
      "\<exists>t. \<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> t \<and> 
       ((\<exists>t'. t =Abrupt t' \<and> snd(l!Suc j) = Normal t') \<or>
       (\<forall>t'. t \<noteq> Abrupt t' \<and> snd(l!Suc j)=t))"
    proof -
      fix t 
      { assume "fst(l!Suc j) = Skip"
        then have step:"\<Gamma>\<turnstile>\<^sub>c (Await b c e,Normal s)  \<rightarrow> (Skip, snd(l!Suc j))"
          using step_await k_basic by fastforce
        have s'_b:"s\<in>b" using s'_in_bp by fastforce
        note step = stepc_elim_cases_Await_skip[OF step]
        have h:"(s \<in> b \<Longrightarrow> \<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> snd(l!Suc j) \<Longrightarrow> \<forall>t'. snd(l!Suc j) \<noteq> Abrupt t' \<Longrightarrow>
              \<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> snd(l!Suc j) \<and> (\<forall>t'. snd(l!Suc j) \<noteq> Abrupt t'))" by auto
        have ?thesis 
          using step[OF h] by fastforce
      } note left = this
      { assume "fst(l!Suc j)= Throw \<and> (\<exists>s1. snd(l!Suc j) = Normal s1)"
        then obtain s1 where step:"fst(l!Suc j)= Throw \<and> snd(l!Suc j) = Normal s1"
          by fastforce
        then have step: "\<Gamma>\<turnstile>\<^sub>c (Await b c e,Normal s)  \<rightarrow> (Throw, snd(l!Suc j))"
          using step_await k_basic by fastforce
        have s'_b:"s\<in>b" using s'_in_bp by fastforce
        note step = stepc_elim_cases_Await_throw[OF step]
        have h:"(\<And>t'. snd(l!Suc j) = Normal t' \<Longrightarrow> s \<in> b \<Longrightarrow> \<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> Abrupt t' \<Longrightarrow> 
                \<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> Abrupt t' \<and>  snd(l!Suc j) = Normal t')"
        by auto                
        have ?thesis using step[OF h] by blast 
      } thus ?thesis using suc_skip  left  step_await suc_skip by blast 
    qed
    then obtain t where e_step:"\<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> t \<and> 
             ((\<exists>t'. t =Abrupt t' \<and> snd(l!Suc j) = Normal t') \<or>
             (\<forall>t'. t \<noteq> Abrupt t' \<and> snd(l!Suc j)=t)) " by fastforce
    moreover have "t \<notin> Fault ` F" 
    proof -           
       {assume a10:"t \<in> Fault ` F"
       then obtain tf where "t=Fault tf \<and> tf\<in>F" by fastforce
       then have "snd(l!Suc j) = Fault tf \<and> tf\<in>F" using e_step by fastforce
       also have "snd(l!Suc j) \<notin> Fault  ` F" 
         using last_not_F[of \<Gamma> l F] a5 a1 step_await a0 by blast
       ultimately have False by auto
       } thus ?thesis by auto
    qed
    ultimately have t_q_a:"t \<in> Normal ` ({s'. (Normal s, Normal s') \<in> G} \<inter>q) \<union> 
                              Abrupt ` ({s'. (Normal s, Normal s') \<in> G} \<inter> a)" 
      using e_auto unfolding valid_def by fastforce
    thus ?thesis using e_step t_q_a  by blast                                                                       
  qed       
  then have "\<forall>i. 0\<le>i \<and> i\<noteq>j \<and> Suc i < (length l) \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))"
    using only_one_component_tran_all_not_comp_await[OF a0 a1] first a3 
          a0 a1 calculation(1) only_one_component_tran1 prg_j by blast 
  moreover then have k:"k=j" using a2 by fastforce
  ultimately have "(\<forall>j. 0\<le>j \<and> j\<noteq>k \<and> Suc j < (length l) \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))))" by auto 
  also from conc k k_basic have 
     "(\<exists>s s'. fst (l!k) = Await b c e \<and> snd (l!k) \<in> Normal ` (p) \<and> snd (l!k) = Normal s \<and> snd (l!Suc k) = Normal s' \<and> 
            (snd (l!Suc k) \<in> Normal ` ({s'. (Normal s, Normal s') \<in> G} \<inter> q) \<or> 
             snd (l!Suc k) \<in> Normal ` ({s'. (Normal s, Normal s') \<in> G} \<inter> a)))"
     by fastforce
  ultimately show ?thesis by auto
qed 

lemma one_component_tran_await_env:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!0) = Await b c e" and         
         a2: "Suc k<length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))" and
         a3: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!0) \<in> Normal ` p \<and> 
                                        Sta q rely \<and>
                                        Sta a rely" and
         a4:"\<forall>V. \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
             (p \<inter> b \<inter> {V}) c
             ({s. (Normal V, Normal s) \<in> G} \<inter> q),
             ({s. (Normal V, Normal s) \<in> G} \<inter> a)" and
         a5:"snd (last l) \<notin> Fault ` F"           
  shows "(\<forall>j. 0\<le>j \<and> j\<noteq>k \<and> Suc j < (length l) \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))) \<and> 
           (\<exists>s s'. fst (l!k) = Await b c e \<and> snd (l!k) \<in> Normal ` (p) \<and> 
                 snd (l!k) = Normal s \<and> snd (l!Suc k) = Normal s' \<and> 
                  (snd (l!Suc k) \<in> Normal ` ({s'. (Normal s, Normal s') \<in> G} \<inter> q) \<or> 
                   snd (l!Suc k) \<in> Normal ` ({s'. (Normal s, Normal s') \<in> G} \<inter> a)))"  
proof - 
  have "(\<forall>j. 0\<le>j \<and> j\<noteq>k \<and> Suc j < (length l) \<longrightarrow> \<not> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))) \<and> 
        (\<exists>s s'. fst (l!k) = Await b c e \<and> snd (l!k) \<in> Normal ` (p) \<and> 
                snd (l!k) = Normal s \<and> snd (l!Suc k) = Normal s' \<and> 
                  (snd (l!Suc k) \<in> Normal ` ({s'. (Normal s, Normal s') \<in> G} \<inter> q) \<or> 
                   snd (l!Suc k) \<in> Normal ` ({s'. (Normal s, Normal s') \<in> G} \<inter> a)))"
  using one_component_tran_await[OF a0 a1 a2 a3 a4 a5] by auto
  thus ?thesis using  a0
  by (metis Suc_eq_plus1 cptn_tran_ce_i step_ce_elim_cases)    
qed

lemma final_exist_component_tran_await:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
          a1: "fst (l!i) = Await b c e" and               
          a2: "env_tran \<Gamma> q l R " and
          a3: "i\<le>j \<and> j < length l \<and> final (l!j)" 
  shows "\<exists>k. k\<ge>i \<and> k<j \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)\<or>(c1 = Throw \<and> (\<exists>s21. s2 =Normal s21 ))" 
    using  await_skip by blast
  thus ?thesis using  a0 a1 a2 a3 final_exist_component_tran by blast
qed   

inductive_cases stepc_elim_cases_Await_Fault:
"\<Gamma>\<turnstile>\<^sub>c (Await b c e, Normal s) \<rightarrow> (u,Fault f)"

lemma Await_sound1: 
 "\<forall>V. \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
    (p \<inter> b \<inter> {V}) e 
    ({s. (Normal V, Normal s) \<in> G} \<inter> q),
    ({s. (Normal V, Normal s) \<in> G} \<inter> a) \<Longrightarrow>     
 Sta p R \<Longrightarrow> Sta q R \<Longrightarrow> Sta a R \<Longrightarrow>   
 c \<in> cp \<Gamma> (Await b e e1) s \<Longrightarrow>
 c \<in> assum(p, R) \<Longrightarrow>
 c \<in> comm (G, (q,a)) F"
proof -  
 assume
  a0: "\<forall>V. \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (p \<inter> b \<inter> {V}) e 
        ({s. (Normal V, Normal s) \<in> G} \<inter> q),
        ({s. (Normal V, Normal s) \<in> G} \<inter> a)" and
  a2:"Sta p R" and
  a3:"Sta q R" and
  a4:"Sta a R" and 
  a10:"c \<in> cp \<Gamma> (Await b e e1) s" and
  a11:"c \<in> assum(p, R)"

  obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
  {assume last_fault:"snd (last l) \<notin> Fault ` F"
   have cp:"l!0=(Await b e e1,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
   have assum:"snd(l!0) \<in> Normal ` (p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
             (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
               (snd(l!i), snd(l!(Suc i))) \<in> R)" 
   using a11 c_prod unfolding assum_def by simp
   have concl:"(\<forall>i ns ns'. Suc i<length l \<longrightarrow> 
           \<Gamma>1\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow>                              
             (snd(l!i), snd(l!(Suc i))) \<in> G)"
   proof -
   { fix k ns ns'
     assume a00:"Suc k<length l" and
            a11:"\<Gamma>1\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))"                
     have len_l:"length l > 0" using cp using cptn.simps by blast 
     then obtain a1 l1 where l:"l=a1#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
     have env_tran:"env_tran \<Gamma> p l R" using assum env_tran_def cp by blast
     then have env_tran_right: "env_tran_right \<Gamma> l R" 
       using env_tran env_tran_right_def unfolding env_tran_def by auto
     then have all_event:
          "(\<exists>s s'. fst (l!k) = Await b e e1 \<and> snd (l!k) \<in> Normal ` (p) \<and> snd (l!k) = 
                   Normal s \<and> snd (l!Suc k) = Normal s' \<and> 
                  (snd (l!Suc k) \<in> Normal ` ({s'. (Normal s, Normal s') \<in> G} \<inter> q) \<or> 
                   snd (l!Suc k) \<in> Normal ` ({s'. (Normal s, Normal s') \<in> G} \<inter> a)))"
       using a00 a11  one_component_tran_await_env[of \<Gamma> l b e e1 k R p q a F G] env_tran_right cp len_l
       using a0 a2 a3 a4 assum fst_conv last_fault by auto                                                                          
     then obtain s' s'' where ss:
       "snd (l!k) = Normal s' \<and> s' \<in> (p) \<and>  snd (l!Suc k) = Normal s'' 
        \<and> (s'' \<in> (({s. (Normal s', Normal s) \<in> G} \<inter> q)) \<or> 
           s''\<in> (({s. (Normal s', Normal s) \<in> G} \<inter> a)))"
     by fastforce 
     then have "(snd(l!k), snd(l!(Suc k))) \<in> G"
       using a2  by force
   } thus ?thesis using c_prod by auto qed  
   have concr:"(final (last l)  \<longrightarrow>                    
               ((fst (last l) = Skip \<and> 
                snd (last l) \<in> Normal ` q)) \<or>
                (fst (last l) = Throw \<and> 
                snd (last l) \<in> Normal ` (a)))"
   proof-
   { 
     assume valid:"final (last l)"         
     have len_l:"length l > 0" using cp using cptn.simps by blast 
     then obtain a1 l1 where l:"l=a1#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
     have last_l:"last l = l!(length l-1)"
       using last_length [of a1 l1] l by fastforce
     have env_tran:"env_tran \<Gamma> p l R" using assum env_tran_def cp by blast
     then have env_tran_right: "env_tran_right \<Gamma> l R" 
       using env_tran env_tran_right_def unfolding env_tran_def by auto
     have "\<exists>k. k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
     proof -             
       have "0\<le> (length l-1)" using len_l last_l by auto
       moreover have "(length l-1) < length l" using len_l by auto
       moreover have "final (l!(length l-1))" using valid last_l by auto
       moreover have "fst (l!0) = Await b e e1" using cp by auto
       ultimately show ?thesis 
         using  cp final_exist_component_tran_await env_tran by blast 
     qed
     then obtain k  where k_comp_tran: "k\<ge>0 \<and> Suc k < length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
       by fastforce
     then obtain ck sk csk ssk where tran_pair:
       "\<Gamma>1\<turnstile>\<^sub>c (ck,sk)  \<rightarrow> (csk, ssk) \<and> (ck = fst (l!k)) \<and> (sk = snd (l!k)) \<and> (csk = fst (l!(Suc k))) \<and> (ssk = snd (l!(Suc k)))" 
       using cp by fastforce         
     have all_event:
          "(\<forall>j. 0\<le>j \<and> j\<noteq>k \<and> Suc j < (length l) \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))) \<and>
           (\<exists>s s'. fst (l!k) = Await b e e1 \<and> snd (l!k) \<in> Normal ` (p) \<and> snd (l!k) = 
                   Normal s \<and> snd (l!Suc k) = Normal s' \<and> 
                  (snd (l!Suc k) \<in> Normal ` ({s'. (Normal s, Normal s') \<in> G} \<inter> q) \<or> 
                   snd (l!Suc k) \<in> Normal ` ({s'. (Normal s, Normal s') \<in> G} \<inter> a)))"
       using  one_component_tran_await_env[of \<Gamma> l b e e1 k R p q a F G] a0 a11 a2 a3 a4 assum cp 
              env_tran_right  len_l  fst_conv last_fault k_comp_tran  by fastforce
     then have before_k_all_evn:"\<forall>j. 0\<le>j \<and> j < k  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
           using k_comp_tran by fastforce
     then obtain s' where k_basic:"ck = Await b e e1 \<and> sk \<in> Normal ` (p) \<and> sk = Normal s'" 
       using cp env_tran_right a2 assum tran_pair k_comp_tran stability[of p R l 0 k k \<Gamma>] tran_pair
       by force        
     have "\<Gamma>\<^sub>\<not>\<^sub>a,{}\<Turnstile>\<^bsub>/F\<^esub> 
                 (p \<inter> b \<inter> {s'}) e 
                 ({s. (Normal s', Normal s) \<in> G} \<inter> q),
                 ({s. (Normal s', Normal s) \<in> G} \<inter> a)"
       using  a0 hoare_sound k_basic
         by fastforce
       then have e_auto:"\<Gamma>\<^sub>\<not>\<^sub>a\<Turnstile>\<^bsub>/F\<^esub> (p \<inter> b \<inter> {s'}) e 
                 ({s. (Normal s', Normal s) \<in> G} \<inter> q),
                 ({s. (Normal s', Normal s) \<in> G} \<inter> a)" 
         unfolding cvalid_def by auto   
     have after_k_all_evn:"\<forall>j. (Suc k)\<le>j \<and> Suc j < (length l)  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
           using all_event k_comp_tran by fastforce          
     have suc_skip: "csk = Skip  \<or> (csk = Throw \<and> (\<exists>s1. ssk = Normal s1))"
        using a0  k_basic tran_pair await_skip by blast
     moreover {
       assume at:"csk = Skip" 
       then have atom_tran:"\<Gamma>\<^sub>\<not>\<^sub>a\<turnstile>\<langle>e,sk\<rangle> \<Rightarrow> ssk"
           using k_basic tran_pair k_basic cp stepc_elim_cases_Await_skip
           by metis
       have sk_in_normal_pb:"sk \<in> Normal ` (p \<inter> b)" 
         using k_basic tran_pair at cp stepc_elim_cases_Await_skip
          by (metis (no_types, lifting) IntI image_iff)                                  
       then have "fst (last l) = Skip \<and> 
                   snd ((last l)) \<in> Normal ` q" 
       proof (cases ssk)
         case (Normal t)                                                  
         then have "ssk \<in> Normal ` q" 
           using sk_in_normal_pb k_basic e_auto Normal atom_tran unfolding valid_def
           by blast
         thus ?thesis
           using at l tran_pair last_l len_l cp 
             env_tran_right a3  after_k_all_evn 
             assum k_comp_tran stability [of q R l "Suc k" "((length l) - 1)" _ \<Gamma>]
           by (metis (no_types, hide_lams) Suc_leI diff_Suc_eq_diff_pred diff_less less_one zero_less_diff)         
       next
          case (Abrupt t)
          thus ?thesis 
           using at k_basic tran_pair k_basic cp stepc_elim_cases_Await_skip
             by metis                
       next
          case (Fault f1)              
          then have "ssk \<in> Normal ` q \<or> ssk \<in> Fault ` F" 
            using k_basic sk_in_normal_pb e_auto Fault atom_tran unfolding valid_def by auto                          
          thus ?thesis
          proof
            assume "ssk \<in> Normal ` q" thus ?thesis using Fault by auto
          next
            assume suck_fault:"ssk \<in> Fault ` F"
            have "\<forall>i<length l. snd (l ! i) \<notin> Fault ` F" 
               using last_not_F[of \<Gamma> l F] last_fault cp by auto
            thus ?thesis 
               using cp tran_pair a11 k_comp_tran suck_fault
               by (meson diff_less len_l less_imp_Suc_add less_one less_trans_Suc)                  
          qed
       next 
          case (Stuck)             
          then have "ssk \<in> Normal ` q" 
           using k_basic sk_in_normal_pb e_auto Stuck atom_tran unfolding valid_def
           by blast
          thus ?thesis using Stuck by auto                             
       qed            
     }
     moreover {
       assume at:"(csk = Throw \<and> (\<exists>t. ssk = Normal t))"
       then obtain t where ssk_normal:"ssk=Normal t" by auto
       then have atom_tran:"\<Gamma>\<^sub>\<not>\<^sub>a\<turnstile>\<langle>e,sk\<rangle> \<Rightarrow> Abrupt t"
           using at k_basic tran_pair k_basic ssk_normal cp stepc_elim_cases_Await_throw xstate.inject(1)
           by metis                        
       also have "sk \<in> Normal ` (p \<inter> b)" 
           using k_basic tran_pair k_basic ssk_normal at cp stepc_elim_cases_Await_throw
           by (metis (no_types, lifting) IntI imageE image_eqI stepc_elim_cases_Await_throw)               
       then have "ssk \<in> Normal ` a" 
         using e_auto k_basic ssk_normal atom_tran unfolding valid_def
         by blast
       then have "(fst (last l) = Throw \<and> snd (last l) \<in> Normal ` (a))"
       using at l tran_pair last_l len_l cp 
           env_tran_right a4  after_k_all_evn
           assum k_comp_tran stability [of a R l "Suc k" "((length l) - 1)" _ \<Gamma>]        
       by (metis (no_types, hide_lams) Suc_leI diff_Suc_eq_diff_pred diff_less less_one zero_less_diff)                    
     }
     ultimately have "fst (last l) = Skip \<and> 
                         snd ((last l)) \<in> Normal ` q \<or>
                        (fst (last l) = Throw \<and> snd (last l) \<in> Normal ` (a))"
     by blast                     
   } thus ?thesis by auto qed
   note res = conjI [OF concl concr]               
  }              
  thus ?thesis using c_prod unfolding comm_def by auto 
qed 
subsection {* If sound *}

lemma cptn_assum_induct:
assumes
  a0: "(\<Gamma>,l) \<in> (cp \<Gamma> c s) \<and> ((\<Gamma>,l) \<in> assum(p, R))" and
  a1: "k < length l \<and> l!k=(c1,Normal s') \<and> s' \<in> p1"
shows "(\<Gamma>,drop k l)\<in> ((cp \<Gamma> c1 (Normal s')) \<inter> assum(p1, R) )"
proof -
  have drop_k_s:"(drop k l)!0 = (c1,Normal s')" using a1 by fastforce
  have p1:"s' \<in> p1" using a1 by auto
  have k_l:"k < length l" using a1 by auto
  show ?thesis
  proof
    show "(\<Gamma>, drop k l) \<in> cp \<Gamma> c1 (Normal s')" 
    unfolding cp_def 
    using dropcptn_is_cptn a0 a1 drop_k_s cp_def 
    by fastforce
  next
    let ?c= "(\<Gamma>,drop k l)"
    have l:"snd((snd ?c!0)) \<in> Normal ` p1"
     using p1 drop_k_s by auto
    {fix i
     assume a00:"Suc i<length (snd ?c)" 
     assume a11:"(fst ?c)\<turnstile>\<^sub>c((snd ?c)!i)  \<rightarrow>\<^sub>e ((snd ?c)!(Suc i))"
     have "(snd((snd ?c)!i), snd((snd ?c)!(Suc i))) \<in> R "
     using a0 unfolding assum_def using a00 a11 by auto
    } thus "(\<Gamma>, drop k l) \<in> assum (p1, R)" 
      using l unfolding assum_def by fastforce  
  qed  
qed

lemma Await_sound: 
 "\<forall>V. \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
    (p \<inter> b \<inter> {V}) e 
    ({s. (Normal V, Normal s) \<in> G} \<inter> q),
    ({s. (Normal V, Normal s) \<in> G} \<inter> a) \<Longrightarrow>     
 Sta p R \<Longrightarrow> Sta q R \<Longrightarrow> Sta a R \<Longrightarrow>   
 \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub>  (Await b e e1) sat [p, R, G, q,a]"
proof -  
 assume
  a0: "\<forall>V. \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (p \<inter> b \<inter> {V}) e 
        ({s. (Normal V, Normal s) \<in> G} \<inter> q),
        ({s. (Normal V, Normal s) \<in> G} \<inter> a)" and
  a2:"Sta p R" and
  a3:"Sta q R" and
  a4:"Sta a R"  
{
    fix s
    have "cpn n \<Gamma> (Await b e e1) s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cpn n \<Gamma> (Await b e e1) s" and a11:"c \<in> assum(p, R)"
      then have a10:"c\<in>cp \<Gamma> (Await b e e1) s"
        using cp_def cpn_def cptn_if_cptn_mod cptn_mod_nest_cptn_mod by blast
      have "c\<in>comm(G, (q,a)) F" using Await_sound1[OF a0 a2 a3 a4 a10 a11] by auto      
    } thus ?thesis by auto
    qed 
  } 
  thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed


lemma cptn_comm_induct:
assumes
  a0: "(\<Gamma>,l) \<in> (cp \<Gamma> c s)" and
  a1: "l1 = drop j l \<and> (\<Gamma>, l1)\<in> comm(G, (q,a)) F" and
  a2: "k \<ge> j \<and> j < length l" 
shows "snd (last (l)) \<notin> Fault ` F  \<longrightarrow> ((Suc k < length l \<longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)) \<longrightarrow>        
       (snd(l!k), snd(l!(Suc k))) \<in> G) 
      \<and> (final (last (l))  \<longrightarrow>           
            ((fst (last (l)) = Skip \<and> 
              snd (last (l)) \<in> Normal ` q)) \<or>
            (fst (last (l)) = Throw \<and> 
              snd (last (l)) \<in> Normal ` (a))))"
proof -  
  have pair_\<Gamma>l:"fst (\<Gamma>,l1) = \<Gamma> \<and> snd (\<Gamma>,l1) = l1" by fastforce  
  have a03:"snd (last (l1)) \<notin> Fault ` F  \<longrightarrow>(\<forall>i.                 
               Suc i<length (snd (\<Gamma>, l1)) \<longrightarrow> 
               fst (\<Gamma>, l1)\<turnstile>\<^sub>c((snd (\<Gamma>, l1))!i)  \<rightarrow> ((snd (\<Gamma>, l1))!(Suc i)) \<longrightarrow>                                             
                 (snd((snd (\<Gamma>, l1))!i), snd((snd (\<Gamma>, l1))!(Suc i))) \<in> G) \<and> 
               (final (last (snd (\<Gamma>, l1)))  \<longrightarrow> 
                snd (last (snd (\<Gamma>, l1))) \<notin> Fault ` F  \<longrightarrow>
                  ((fst (last (snd (\<Gamma>, l1))) = Skip \<and> 
                    snd (last (snd (\<Gamma>, l1))) \<in> Normal ` q)) \<or>
                  (fst (last (snd (\<Gamma>, l1))) = Throw \<and> 
                    snd (last (snd (\<Gamma>, l1))) \<in> Normal ` (a)))"
  using a1 unfolding comm_def by fastforce
  have last_l:"last l1 = last l" using a1 a2 by fastforce
  show ?thesis  
  proof -
  {
    assume " snd (last l) \<notin> Fault ` F" 
    then have l1_f:"snd (last l1) \<notin> Fault ` F" 
     using a03 a1 a2 by force        
      { assume "Suc k < length l"
      then have a2: "k \<ge> j \<and> Suc k < length l" using a2 by auto
      have "k \<le> length l" using a2 by fastforce
      then have l1_l:"(l!k = l1! (k - j) ) \<and> (l!Suc k = l1!Suc (k - j))"
        using a1 a2 by fastforce    
      have a00:"Suc (k - j) < length l1" using a1 a2 by fastforce
      have "\<Gamma>\<turnstile>\<^sub>c(l1!(k-j))  \<rightarrow> (l1!(Suc (k-j))) \<longrightarrow>         
        (snd((snd (\<Gamma>, l1))!(k-j)), snd((snd (\<Gamma>, l1))!(Suc (k-j)))) \<in> G"
      using  pair_\<Gamma>l a00 l1_f a03 by presburger
      then have " \<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)) \<longrightarrow> 
        (snd (l ! k), snd (l ! Suc k)) \<in> G " 
        using l1_l last_l by auto
    } then have l_side:"Suc k < length l \<longrightarrow>
    \<Gamma>\<turnstile>\<^sub>c l ! k \<rightarrow> l ! Suc k \<longrightarrow>   
    (snd (l ! k), snd (l ! Suc k)) \<in> G" by auto 
    { 
      assume a10:"final (last (l))"              
      then have final_eq: "final (last (l1))"
        using a10 a1 a2 by fastforce
      also have "snd (last (l1)) \<notin> Fault ` F"
        using last_l l1_f by fastforce
      ultimately have "((fst (last (snd (\<Gamma>, l1))) = Skip \<and> 
                        snd (last (snd (\<Gamma>, l1))) \<in> Normal ` q)) \<or>
                      (fst (last (snd (\<Gamma>, l1))) = Throw \<and> 
                        snd (last (snd (\<Gamma>, l1))) \<in> Normal ` (a))"
        using pair_\<Gamma>l a03 by presburger
      then have "((fst (last (snd (\<Gamma>, l))) = Skip \<and> 
              snd (last (snd (\<Gamma>, l))) \<in> Normal ` q)) \<or>
              (fst (last (snd (\<Gamma>, l))) = Throw \<and> 
             snd (last (snd (\<Gamma>, l))) \<in> Normal ` (a))"
        using final_eq a1 a2 by auto 
     } then have 
      r_side: 
      "SmallStepCon.final (last l) \<longrightarrow>     
      fst (last l) = LanguageCon.com.Skip \<and> snd (last l) \<in> Normal ` q \<or>
       fst (last l) = LanguageCon.com.Throw \<and> snd (last l) \<in> Normal ` a"
       by fastforce
     note res=conjI[OF l_side r_side] 
   } thus ?thesis by auto
   qed
qed

lemma cpn_assum_induct:
assumes
  a0: "(\<Gamma>,l) \<in> (cpn n \<Gamma> c s) \<and> ((\<Gamma>,l) \<in> assum(p, R))" and
  a1: "k < length l \<and> l!k=(c1,Normal s') \<and> s' \<in> p1"
shows "(\<Gamma>,drop k l)\<in> ((cpn n \<Gamma> c1 (Normal s')) \<inter> assum(p1, R) )"
proof -
  have drop_k_s:"(drop k l)!0 = (c1,Normal s')" using a1 by fastforce
  have p1:"s' \<in> p1" using a1 by auto
  have k_l:"k < length l" using a1 by auto
  show ?thesis
  proof
    show "(\<Gamma>, drop k l) \<in> cpn n \<Gamma> c1 (Normal s')" 
    unfolding cp_def 
    using  a0 a1  
    by (simp add: cpn_def dropcptn_is_cptn1) 
  next
    let ?c= "(\<Gamma>,drop k l)"
    have l:"snd((snd ?c!0)) \<in> Normal ` p1"
     using p1 drop_k_s by auto
    {fix i
     assume a00:"Suc i<length (snd ?c)" 
     assume a11:"(fst ?c)\<turnstile>\<^sub>c((snd ?c)!i)  \<rightarrow>\<^sub>e ((snd ?c)!(Suc i))"
     have "(snd((snd ?c)!i), snd((snd ?c)!(Suc i))) \<in> R "
     using a0 unfolding assum_def using a00 a11 by auto
    } thus "(\<Gamma>, drop k l) \<in> assum (p1, R)" 
      using l unfolding assum_def by fastforce  
  qed  
qed

lemma cpn_comm_induct:
  assumes
  a1: "l1 = drop j l \<and> (\<Gamma>, l1)\<in> comm(G, (q,a)) F" and
  a2: "k \<ge> j \<and> j < length l" 
shows "snd (last (l)) \<notin> Fault ` F  \<longrightarrow> ((Suc k < length l \<longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)) \<longrightarrow>        
       (snd(l!k), snd(l!(Suc k))) \<in> G) 
      \<and> (final (last (l))  \<longrightarrow>           
            ((fst (last (l)) = Skip \<and> 
              snd (last (l)) \<in> Normal ` q)) \<or>
            (fst (last (l)) = Throw \<and> 
              snd (last (l)) \<in> Normal ` (a))))"
proof -  
  have pair_\<Gamma>l:"fst (\<Gamma>,l1) = \<Gamma> \<and> snd (\<Gamma>,l1) = l1" by fastforce  
  have a03:"snd (last (l1)) \<notin> Fault ` F  \<longrightarrow>(\<forall>i.                 
               Suc i<length (snd (\<Gamma>, l1)) \<longrightarrow> 
               fst (\<Gamma>, l1)\<turnstile>\<^sub>c((snd (\<Gamma>, l1))!i)  \<rightarrow> ((snd (\<Gamma>, l1))!(Suc i)) \<longrightarrow>                                             
                 (snd((snd (\<Gamma>, l1))!i), snd((snd (\<Gamma>, l1))!(Suc i))) \<in> G) \<and> 
               (final (last (snd (\<Gamma>, l1)))  \<longrightarrow> 
                snd (last (snd (\<Gamma>, l1))) \<notin> Fault ` F  \<longrightarrow>
                  ((fst (last (snd (\<Gamma>, l1))) = Skip \<and> 
                    snd (last (snd (\<Gamma>, l1))) \<in> Normal ` q)) \<or>
                  (fst (last (snd (\<Gamma>, l1))) = Throw \<and> 
                    snd (last (snd (\<Gamma>, l1))) \<in> Normal ` (a)))"
  using a1 unfolding comm_def by fastforce
  have last_l:"last l1 = last l" using a1 a2 by fastforce
  show ?thesis  
  proof -
  {
    assume " snd (last l) \<notin> Fault ` F" 
    then have l1_f:"snd (last l1) \<notin> Fault ` F" 
     using a03 a1 a2 by force        
      { assume "Suc k < length l"
      then have a2: "k \<ge> j \<and> Suc k < length l" using a2 by auto
      have "k \<le> length l" using a2 by fastforce
      then have l1_l:"(l!k = l1! (k - j) ) \<and> (l!Suc k = l1!Suc (k - j))"
        using a1 a2 by fastforce    
      have a00:"Suc (k - j) < length l1" using a1 a2 by fastforce
      have "\<Gamma>\<turnstile>\<^sub>c(l1!(k-j))  \<rightarrow> (l1!(Suc (k-j))) \<longrightarrow>         
        (snd((snd (\<Gamma>, l1))!(k-j)), snd((snd (\<Gamma>, l1))!(Suc (k-j)))) \<in> G"
      using  pair_\<Gamma>l a00 l1_f a03 by presburger
      then have " \<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)) \<longrightarrow> 
        (snd (l ! k), snd (l ! Suc k)) \<in> G " 
        using l1_l last_l by auto
    } then have l_side:"Suc k < length l \<longrightarrow>
    \<Gamma>\<turnstile>\<^sub>c l ! k \<rightarrow> l ! Suc k \<longrightarrow>   
    (snd (l ! k), snd (l ! Suc k)) \<in> G" by auto 
    { 
      assume a10:"final (last (l))"              
      then have final_eq: "final (last (l1))"
        using a10 a1 a2 by fastforce
      also have "snd (last (l1)) \<notin> Fault ` F"
        using last_l l1_f by fastforce
      ultimately have "((fst (last (snd (\<Gamma>, l1))) = Skip \<and> 
                        snd (last (snd (\<Gamma>, l1))) \<in> Normal ` q)) \<or>
                      (fst (last (snd (\<Gamma>, l1))) = Throw \<and> 
                        snd (last (snd (\<Gamma>, l1))) \<in> Normal ` (a))"
        using pair_\<Gamma>l a03 by presburger
      then have "((fst (last (snd (\<Gamma>, l))) = Skip \<and> 
              snd (last (snd (\<Gamma>, l))) \<in> Normal ` q)) \<or>
              (fst (last (snd (\<Gamma>, l))) = Throw \<and> 
             snd (last (snd (\<Gamma>, l))) \<in> Normal ` (a))"
        using final_eq a1 a2 by auto 
     } then have 
      r_side: 
      "SmallStepCon.final (last l) \<longrightarrow>     
      fst (last l) = LanguageCon.com.Skip \<and> snd (last l) \<in> Normal ` q \<or>
       fst (last l) = LanguageCon.com.Throw \<and> snd (last l) \<in> Normal ` a"
       by fastforce
     note res=conjI[OF l_side r_side] 
   } thus ?thesis by auto
   qed
qed


lemma If_sound: 
      "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> b,  R, G, q,a] \<Longrightarrow>
       (\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> b,  R, G, q,a]) \<Longrightarrow>
       \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [p \<inter> (-b),  R, G, q,a] \<Longrightarrow>
       (\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c2 sat [p \<inter> (-b),  R, G, q,a]) \<Longrightarrow>      
       Sta p R \<Longrightarrow> (\<forall>s. (Normal s, Normal s) \<in> G)  \<Longrightarrow> 
       \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (Cond b c1 c2) sat [p, R, G, q,a]"
proof -  
 assume
    a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> b,  R, G, q,a]" and
    a1:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [p \<inter> (-b), R, G, q,a]" and    
    a2: "\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> b, R, G, q,a]" and
    a3: "\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c2 sat [p \<inter> (-b), R, G, q,a]" and
    a4: "Sta p R" and
    a5: "(\<forall>s. (Normal s, Normal s) \<in> G)"
  { 
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"
    then have a3:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c2 sat [p \<inter> (-b), R, G, q,a]" 
      using a3 com_cvalidityn_def  by fastforce 
    have a2:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> b, R, G, q,a]"
      using a2 all_call com_cvalidityn_def  by fastforce 
    have "cpn n \<Gamma> (Cond b c1 c2)  s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cpn n \<Gamma> (Cond b c1 c2) s" and a11:"c \<in> assum(p, R)"
      then have a10':"c \<in> cp \<Gamma> (Cond b c1 c2) s" unfolding cp_def cpn_def
        using cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod by fastforce
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof - 
      {assume l_f:"snd (last l) \<notin> Fault ` F"  
       
       have cp:"l!0=((Cond b c1 c2),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10' cp_def c_prod by fastforce
       have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast
       have assum:"snd(l!0) \<in> Normal ` (p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                   (snd(l!i), snd(l!(Suc i))) \<in> R)" 
       using a11 c_prod unfolding assum_def by simp
       then have env_tran:"env_tran \<Gamma> p l R" using env_tran_def cp by blast
       then have env_tran_right: "env_tran_right \<Gamma> l R" 
         using env_tran env_tran_right_def unfolding env_tran_def by auto
       have concl:"(\<forall>i. Suc i<length l \<longrightarrow> 
               \<Gamma>1\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow>               
                 (snd(l!i), snd(l!(Suc i))) \<in> G)"
       proof -
       { fix k ns ns'
         assume a00:"Suc k<length l" and
                a21:"\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))"                                                                           
         obtain j where before_k_all_evnt:"j\<le>k \<and>  (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<and> (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
           using a00 a21 exist_first_comp_tran cp by blast
         then obtain cj sj csj ssj where pair_j:"(\<Gamma>\<turnstile>\<^sub>c(cj,sj)  \<rightarrow> (csj,ssj)) \<and> cj = fst (l!j) \<and> sj = snd (l!j) \<and> csj = fst (l!(Suc j)) \<and> ssj = snd(l!(Suc j))"
           by fastforce                                   
         have k_basic:"cj = (Cond b c1 c2) \<and> sj \<in> Normal ` (p)" 
           using pair_j before_k_all_evnt cp env_tran_right a4 assum a00 stability[of p R l 0 j j \<Gamma>]
         by force
         then obtain s' where ss:"sj = Normal s' \<and> s'\<in> (p)" by auto 
         then have ssj_normal_s:"ssj = Normal s'" using before_k_all_evnt k_basic pair_j
           by (metis prod.collapse snd_conv stepc_Normal_elim_cases(6))          
         have "(snd(l!k), snd(l!(Suc k))) \<in> G"
           using ss a2 unfolding Satis_def         
         proof (cases "k=j")   
           case True          
             have "(Normal s', Normal s') \<in> G" 
               using a5  by blast
             thus "(snd (l ! k), snd (l ! Suc k)) \<in> G"
               using pair_j k_basic True ss ssj_normal_s by auto
         next
           case False
           have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce 
           have l_suc:"l!(Suc j) = (csj, Normal s')" 
             using before_k_all_evnt pair_j  ssj_normal_s
             by fastforce
           have l_k:"j<k" using  before_k_all_evnt False by fastforce
           have "s'\<in>b \<or> s'\<notin>b" by auto                         
           thus "(snd (l ! k), snd (l ! Suc k)) \<in> G"
           proof
             assume a000:"s'\<in>b"
             then have cj:"csj=c1" using k_basic pair_j ss 
               by (metis (no_types) fst_conv stepc_Normal_elim_cases(6))
             moreover have p1:"s' \<in> (p \<inter> b)" using a000 ss by blast              
             moreover  have "cpn n \<Gamma> csj ssj \<inter> assum((p \<inter> b), R) \<subseteq> comm(G, (q,a)) F"
               using calculation a2 com_validityn_def cj by blast             
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
               using l_suc j_length a10 a11 \<Gamma>1  ssj_normal_s
                     cpn_assum_induct[of \<Gamma> l n "(LanguageCon.com.Cond b c1 c2)" s p R  "Suc j" c1 s' "(p \<inter> b)"]
               by blast                         
             show ?thesis 
               using l_k drop_comm a00 a21  a10 \<Gamma>1 l_f  
               cpn_comm_induct
               by fastforce                       
           next
             assume a000:"s'\<notin>b"
              then have cj:"csj=c2" using k_basic pair_j ss 
                  by (metis (no_types) fst_conv stepc_Normal_elim_cases(6))
             moreover have p1:"s' \<in> (p \<inter> (-b))" using a000 ss by fastforce
             moreover then have "cpn n \<Gamma> csj ssj \<inter> assum((p \<inter> (-b)), R)  \<subseteq> comm(G, (q,a)) F"
               using a3 com_validityn_def cj by blast             
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
               using l_suc j_length a10 a11 \<Gamma>1  ssj_normal_s
                     cpn_assum_induct[of \<Gamma> l n "(LanguageCon.com.Cond b c1 c2)" s p R  "Suc j" c2 s' "(p \<inter> (-b))"]
               by fastforce             
             show ?thesis 
             using l_k drop_comm a00 a21 a10 \<Gamma>1 l_f
             cpn_comm_induct
             unfolding Satis_def by fastforce
           qed
         qed 
       } thus ?thesis by (simp add: c_prod cp) qed
       have concr:"(final (last l)  \<longrightarrow>                    
                   ((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` q)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (a)))"
       proof-
       { 
         assume valid:"final (last l)" 
         assume not_fault:  "snd (last l) \<notin> Fault ` F"                 
         have "\<exists>k. k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))) \<and> final (l!(Suc k))"
         proof -             
           have len_l:"length l > 0" using cp using cptn.simps by blast 
           then obtain a1 l1 where l:"l=a1#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
           have last_l:"last l = l!(length l-1)"
             using last_length [of a1 l1] l by fastforce
           have final_0:"\<not>final(l!0)" using cp unfolding final_def by auto
           have "0\<le> (length l-1)" using len_l last_l by auto
           moreover have "(length l-1) < length l" using len_l by auto
           moreover have "final (l!(length l-1))" using valid last_l by auto
           moreover have "fst (l!0) = LanguageCon.com.Cond b c1 c2" using cp by auto
           ultimately show ?thesis 
             using cp final_exist_component_tran_final env_tran_right final_0  
             by blast 
         qed
        then obtain k where a21: "k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))) \<and> final (l!(Suc k))"
           by auto
        then have a00:"Suc k<length l" by fastforce
        then obtain j where before_k_all_evnt:"j\<le>k \<and>  (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<and> (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
           using a00 a21 exist_first_comp_tran cp by blast
       then obtain cj sj csj ssj where pair_j:"(\<Gamma>\<turnstile>\<^sub>c(cj,sj)  \<rightarrow> (csj,ssj)) \<and> cj = fst (l!j) \<and> sj = snd (l!j) \<and> csj = fst (l!(Suc j)) \<and> ssj = snd(l!(Suc j))"
         by fastforce
       have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce                                 
       then have k_basic:"cj = (Cond b c1 c2) \<and> sj \<in> Normal ` (p)" 
         using  pair_j before_k_all_evnt cp env_tran_right a4 assum a00 stability[of p R l 0 j j \<Gamma>]
       by fastforce
       then obtain s' where ss:"sj = Normal s' \<and> s'\<in> (p)" by auto 
       then have ssj_normal_s:"ssj = Normal s'" using before_k_all_evnt k_basic pair_j
         by (metis prod.collapse snd_conv stepc_Normal_elim_cases(6))       
       have l_suc:"l!(Suc j) = (csj, Normal s')" 
           using before_k_all_evnt pair_j  ssj_normal_s
           by fastforce
       have "s'\<in>b \<or> s'\<notin>b" by auto 
       then have "((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` q)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (a))"
       proof
         assume a000:"s'\<in>b"
         then have cj:"csj=c1" using k_basic pair_j ss 
                  by (metis (no_types) fst_conv stepc_Normal_elim_cases(6))
         moreover have p1:"s' \<in> (p \<inter> b)" using a000 ss by blast 
         moreover then have "cpn n \<Gamma> csj ssj \<inter> assum((p \<inter> b), R)  \<subseteq> comm(G, (q,a)) F"
           using a2 com_validityn_def cj by blast         
         ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
           using l_suc j_length a10 a11 \<Gamma>1  ssj_normal_s
                 cpn_assum_induct[of \<Gamma> l n "(LanguageCon.com.Cond b c1 c2)" s p R  "Suc j" c1 s' "(p \<inter> b)"]
           by blast                   
         thus ?thesis       
           using j_length drop_comm   a10 \<Gamma>1  cpn_comm_induct valid not_fault 
           by blast
       next
         assume a000:"s'\<notin>b"
         then have cj:"csj=c2" using k_basic pair_j ss 
                  by (metis (no_types) fst_conv stepc_Normal_elim_cases(6))
         moreover have p1:"s'\<in>(p \<inter> (-b))" using a000 ss by blast 
         moreover then have "cpn n \<Gamma> csj ssj \<inter> assum((p \<inter> (-b)), R)  \<subseteq> comm(G, (q,a)) F"
           using a3 com_validityn_def cj by blast         
         ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
           using l_suc j_length a10 a11 \<Gamma>1  ssj_normal_s
                 cpn_assum_induct[of \<Gamma> l n "(LanguageCon.com.Cond b c1 c2)" s p R  "Suc j" c2 s' "(p \<inter> (-b))"]
           by blast                   
         thus ?thesis       
           using j_length drop_comm a10 \<Gamma>1  cpn_comm_induct valid not_fault 
           by blast
       qed
       } thus ?thesis using l_f by fastforce qed
       note res = conjI [OF concl concr]              
      }             
      thus ?thesis using c_prod  unfolding comm_def by auto  qed      
    } thus ?thesis by auto qed 
} thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed


lemma Asm_sound:
   "(c, p, R, G, q, a) \<in> \<Theta> \<Longrightarrow>    
    \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]
   "
proof -
  assume
   a0:"(c, p, R, G, q, a) \<in> \<Theta>"    
   { fix s
     assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p,  R, G, q,a]"
     then have "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]" using a0 by auto
   } thus ?thesis unfolding com_cvalidityn_def by auto
qed

lemma events_p:
  assumes  a0:"(\<Gamma>,cfg#l)\<in>cptn" and
   a1:"(\<Gamma>,cfg#l) \<in> assum (p,R)" and
   a2:"i<length (cfg#l)" and
   a3:"\<forall>k\<le>i. fst ((cfg#l)!k) = fst cfg" and
   a4:"Sta p R " 
 shows "\<exists>t1. snd((cfg#l)!i)=Normal t1 \<and> t1 \<in> p" 
  using a2 a3
proof(induct i)
  case 0
  then show ?case using a1 a2 unfolding assum_def by auto
next
  case (Suc n)
  then have "\<exists>t1. snd ((cfg # l) ! n) = Normal t1 \<and> t1 \<in> p" by auto 
  moreover have "\<Gamma>\<turnstile>\<^sub>c ((cfg#l)!n) \<rightarrow>\<^sub>e ((cfg#l)!(Suc n))" using Suc a0
    by (metis Env calculation less_Suc_eq_le less_not_refl nat_le_linear prod.collapse)
  then have  "(snd ((cfg#l)!n),snd ((cfg#l)!(Suc n)))\<in>R" using a1 Suc(2) 
    unfolding assum_def by auto
  ultimately show ?case using a4 unfolding Sta_def by auto
qed


lemma not_val_zero:"c \<in> dom \<Gamma> \<Longrightarrow> Sta p R \<Longrightarrow> \<Gamma> \<Turnstile>0\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]"
proof-
  assume a0:" c \<in> dom \<Gamma>"
  assume a1:"Sta p R"
  {fix l s
    assume a01:"(\<Gamma>,l) \<in> cpn 0 \<Gamma> (Call c) s \<and> (\<Gamma>,l)\<in> assum(p, R)"    
    then have "length l \<ge> 1" unfolding cpn_def using CptnEmpty
      by (metis (no_types, lifting) One_nat_def Product_Type.Collect_case_prodD Suc_leI length_greater_0_conv snd_conv)
    moreover {assume a02:"length l = 1"
      then have "l = [(Call c,s)]" 
      proof -
        have "l ! 0 = (LanguageCon.com.Call c, s)" using a01 unfolding cpn_def
          by fastforce
        then show ?thesis using a02
          by (metis One_nat_def Suc_leI impossible_Cons length_greater_0_conv list.size(3) neq_Nil_conv nth_Cons_0 zero_neq_one) 
      qed 
      then have "(\<Gamma>,l) \<in> comm(G, (q,a)) F" unfolding comm_def final_def by auto
    }
    moreover {assume a02:"length l > 1"
      then obtain a1 ls where l:"l =(Call c, s)#a1#ls" using a01 unfolding cpn_def
        apply auto
        by (metis (no_types, hide_lams) One_nat_def Suc_eq_plus1 less_not_refl list.exhaust list.size(3) list.size(4) not_less_zero nth_Cons_0 prod.collapse)   
      have l_cptn:"(\<Gamma>,l)\<in>cptn" using a01 unfolding cpn_def
        using cptn_eq_cptn_mod_nest by blast
      then obtain m where min_call:"min_call m \<Gamma> l"
          using cptn_eq_cptn_mod_set cptn_mod_cptn_mod_nest minimum_nest_call by blast
      { assume a03:"\<forall>i<length l. fst (l!i) = Call c"        
        then have "(\<Gamma>,l) \<in> comm(G, (q,a)) F" 
          using no_comp_tran_no_final_comm[OF _ a03] a02 unfolding final_def
          by fastforce 
      }
      moreover { assume a03:"\<not> (\<forall>i<length l. fst (l!i) = Call c)"
        then obtain i where i:"(i<length l \<and> fst (l!i) \<noteq> Call c)"
          by auto
        then obtain j where cfg_j:"fst (l!j) \<noteq> Call c \<and> (\<forall>k<j. fst (l!k) = Call c)"                     
          by (fast dest: exists_first_occ[of "\<lambda>i. fst (l!i) \<noteq> Call c" i])
        moreover have j:"j>0 \<and> j<length l" using l i calculation
          by (metis gr0I fstI leI le_less_trans nth_Cons') 
        ultimately have step:"(\<Gamma>\<turnstile>\<^sub>c (l!(j-1)) \<rightarrow> (l!j))"
          using l l_cptn
          by (metis One_nat_def Suc_pred cptn_stepc_rtran diff_less not_eq_not_env prod.collapse 
                   step_ce_elim_cases zero_less_one)
        moreover obtain s' where j_1_cfg:"snd (l!(j-1)) = Normal s' \<and> s' \<in> p"
          using cfg_j l a01[simplified l] j[simplified l] i a1 events_p[OF l_cptn[simplified l] _ _ _ a1, of "j-1"]
          by force
        then have j_cfg:"l!j = (the (\<Gamma> c), Normal s')" using cfg_j a0
           stepc_Normal_elim_cases(9) calculation
          by (metis diff_less domIff j option.sel prod.collapse zero_less_one)        
        ultimately have False
        proof-
          have "(0,\<Gamma>, drop (j-1) l) \<in> cptn_mod_nest_call" 
            using a01 unfolding cpn_def 
            by (simp add: dropcptn_is_cptn1 j less_imp_diff_less)      
          then show ?thesis 
            using redex_call_cptn_mod_min_nest_call_gr_zero  j j_cfg j_1_cfg cfg_j step a0
            by (metis Cons_nth_drop_Suc One_nat_def SmallStepCon.redex.simps(7) Suc_pred  
                 diff_less domIff less_imp_diff_less min_call_def not_less_zero prod.collapse 
                 stepc_Normal_elim_cases(9) zero_less_one)             
        qed          
      }
      ultimately have "(\<Gamma>,l) \<in> comm(G, (q,a)) F" by auto
    }
    ultimately have "(\<Gamma>,l)\<in>comm(G, (q,a)) F" by fastforce
  } then show ?thesis unfolding com_validityn_def cpn_def by auto    
qed

lemma Call_sound: 
      "f \<in> dom \<Gamma> \<Longrightarrow>      
       \<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (the (\<Gamma> f)) sat [p, R, G, q,a] \<Longrightarrow>         
       Sta p R \<Longrightarrow> (\<forall>s. (Normal s,Normal s) \<in> G)  \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (Call f) sat [p, R, G, q,a]"
proof -  
  assume
    a0:"f \<in> dom \<Gamma>" and
    a2:"\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (the (\<Gamma> f)) sat [p, R, G, q,a]" and        
    a3: "Sta p R" and
    a4: "(\<forall>s. (Normal s, Normal s) \<in> G)"         
  obtain bdy where a0:"\<Gamma> f = Some bdy" using a0 by auto
  { 
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p,  R, G, q,a]"  
    then have a2:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> bdy sat [p, R, G, q,a]" 
      using a0 a2 com_cvalidityn_def by fastforce
    have "cpn n \<Gamma> (Call f)  s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cpn n \<Gamma> (Call f) s" and a11:"c \<in> assum(p, R)"
      then have a10':"c \<in> cp \<Gamma> (Call f) s" 
        unfolding cpn_def cp_def using cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod by fastforce
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof - 
      {assume l_f:"snd (last l) \<notin> Fault ` F"       
        have cp:"l!0=((Call f),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10' cp_def c_prod by fastforce
        have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast
        have assum:"snd(l!0) \<in> Normal ` (p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                   (snd(l!i), snd(l!(Suc i))) \<in> R)" 
       using a11 c_prod unfolding assum_def by simp
       then have env_tran:"env_tran \<Gamma> p l R" using env_tran_def cp by blast
       then have env_tran_right: "env_tran_right \<Gamma> l R" 
         using env_tran env_tran_right_def unfolding env_tran_def by auto
       have concl:"(\<forall>i. Suc i<length l \<longrightarrow> 
               \<Gamma>1\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow>                              
                 (snd(l!i), snd(l!(Suc i))) \<in> G)"
       proof -
       { fix k ns ns'
         assume a00:"Suc k<length l" and
                a21:"\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))"                                                      
         obtain j where before_k_all_evnt:"j\<le>k \<and>  (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<and> (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
           using a00 a21 exist_first_comp_tran cp by blast
         then obtain cj sj csj ssj where pair_j:"(\<Gamma>\<turnstile>\<^sub>c(cj,sj)  \<rightarrow> (csj,ssj)) \<and> cj = fst (l!j) \<and> sj = snd (l!j) \<and> csj = fst (l!(Suc j)) \<and> ssj = snd(l!(Suc j))"
           by fastforce                                             
         have k_basic:"cj = (Call f) \<and> sj \<in> Normal ` (p)" 
           using  pair_j before_k_all_evnt cp env_tran_right a3 assum a00 stability[of p R l 0 j j \<Gamma>]
           by force
         then obtain s' where ss:"sj = Normal s' \<and> s'\<in> (p)" by auto 
         then have ssj_normal_s:"ssj = Normal s'" 
           using before_k_all_evnt k_basic pair_j a0 
           by (metis not_None_eq snd_conv stepc_Normal_elim_cases(9))                     
         have "(snd(l!k), snd(l!(Suc k))) \<in> G"
           using ss a2 
         proof (cases "k=j")   
           case True                                  
           have "(Normal s', Normal s') \<in> G" 
             using a4 by fastforce 
           thus "(snd (l ! k), snd (l ! Suc k)) \<in> G"
             using pair_j k_basic True ss ssj_normal_s by auto
         next
           case False   
           have j_k:"j<k" using  before_k_all_evnt False by fastforce                      
           thus "(snd (l ! k), snd (l ! Suc k)) \<in>  G"
           proof -
             have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce
             have cj:"csj=bdy" using k_basic pair_j ss a0
               by (metis fst_conv option.distinct(1) option.sel stepc_Normal_elim_cases(9))                
             moreover have p1:"s'\<in>p" using ss by blast 
             moreover then have "cpn n \<Gamma> csj ssj \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
               using a2 com_validityn_def cj by blast
             moreover then have "l!(Suc j) = (csj, Normal s')" 
               using before_k_all_evnt pair_j cj ssj_normal_s
               by fastforce
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
               using  j_length a10 a11 \<Gamma>1  ssj_normal_s                     
               by (meson contra_subsetD cpn_assum_induct)                                
             then show ?thesis 
             using a00 a21  \<Gamma>1  j_k j_length l_f
             cptn_comm_induct[of \<Gamma> l "Call f" s _ "Suc j" G q a F k ]             
             Suc_leI a10' by blast                 
          qed            
       qed 
       } thus ?thesis by (simp add: c_prod cp) qed
       have concr:"(final (last l)  \<longrightarrow>                   
                   ((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` q)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (a)))"
       proof-
       { 
         assume valid:"final (last l)"                       
         have "\<exists>k. k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))) \<and> final (l!(Suc k))"
         proof -             
           have len_l:"length l > 0" using cp using cptn.simps by blast 
           then obtain a1 l1 where l:"l=a1#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
           have last_l:"last l = l!(length l-1)"
            using last_length [of a1 l1] l by fastforce         
           have final_0:"\<not>final(l!0)" using cp unfolding final_def by auto
           have "0\<le> (length l-1)" using len_l last_l by auto
           moreover have "(length l-1) < length l" using len_l by auto
           moreover have "final (l!(length l-1))" using valid last_l by auto
           moreover have "fst (l!0) = Call f" using cp by auto
           ultimately show ?thesis 
             using  cp final_exist_component_tran_final env_tran_right final_0 
             by blast 
          qed
          then obtain k where a21: "k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))) \<and> final (l!(Suc k))"
            by auto
          then have a00:"Suc k<length l" by fastforce
          then obtain j where before_k_all_evnt:"j\<le>k \<and>  (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<and> (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
            using a00 a21 exist_first_comp_tran cp by blast
          then obtain cj sj csj ssj where pair_j:"(\<Gamma>\<turnstile>\<^sub>c(cj,sj)  \<rightarrow> (csj,ssj)) \<and> cj = fst (l!j) \<and> sj = snd (l!j) \<and> csj = fst (l!(Suc j)) \<and> ssj = snd(l!(Suc j))"
            by fastforce         
          have "((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` q)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (a))"
          proof -
            have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce                                 
            then have k_basic:"cj = (Call f) \<and> sj \<in> Normal ` (p)" 
              using  pair_j before_k_all_evnt cp env_tran_right a3 assum a00 stability[of p R l 0 j j \<Gamma>]
              by force
            then obtain s' where ss:"sj = Normal s' \<and> s'\<in> (p)" by auto 
            then have ssj_normal_s:"ssj = Normal s'" 
              using before_k_all_evnt k_basic pair_j a0 
              by (metis not_None_eq snd_conv stepc_Normal_elim_cases(9))
            have cj:"csj=bdy" using k_basic pair_j ss a0
              by (metis fst_conv option.distinct(1) option.sel stepc_Normal_elim_cases(9))                
            moreover have p1:"s'\<in>p" using ss by blast 
            moreover then have "cpn n \<Gamma> csj ssj \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
              using a2 com_validityn_def cj by blast
            moreover then have "l!(Suc j) = (csj, Normal s')" 
              using before_k_all_evnt pair_j cj ssj_normal_s
              by fastforce
            ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
              using  j_length a10 a11 \<Gamma>1  ssj_normal_s              
              by (meson contra_subsetD cpn_assum_induct)              
            thus ?thesis       
              using j_length l_f drop_comm a10' \<Gamma>1 cptn_comm_induct[of \<Gamma> l "Call f" s _ "Suc j" G q a F "Suc j"] valid  
              by blast
           qed
         } thus ?thesis by auto 
         qed
       note res = conjI [OF concl concr]}               
       thus ?thesis using  c_prod unfolding comm_def by force qed      
    } thus ?thesis by auto qed 
  } thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed
           
lemma CallRec_sound:
    "(c, p, R, G, q, a) \<in> Specs \<Longrightarrow>
     \<forall>(c, p, R, G, q, a)\<in>Specs.
       c \<in> dom \<Gamma> \<and>
       Sta p R \<and>  (\<forall>s. (Normal s,Normal s) \<in> G) \<and>      
       \<Gamma>,\<Theta> \<union> Specs \<turnstile>\<^bsub>/F\<^esub> the (\<Gamma> c) sat [p, R, G, q,a] \<and> 
       (\<forall>x. \<Gamma>,\<Theta> \<union> Specs \<Turnstile>x \<^bsub>/F\<^esub> the (\<Gamma> c) sat [p,R, G, q,a]) \<Longrightarrow>
    Sta p R \<Longrightarrow> (\<forall>s. (Normal s,Normal s) \<in> G) \<Longrightarrow>
     \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]"
proof -
  assume a0: "(c, p, R, G, q, a) \<in> Specs" and
     a1: 
    "\<forall>(c, p, R, G, q, a)\<in>Specs.
       c \<in> dom \<Gamma> \<and> Sta p R \<and> (\<forall>s. (Normal s,Normal s) \<in> G) \<and>  
       \<Gamma>,\<Theta> \<union> Specs \<turnstile>\<^bsub>/F\<^esub> the (\<Gamma> c) sat [p, R, G, q,a] \<and> 
       (\<forall>x. \<Gamma>,\<Theta> \<union> Specs \<Turnstile>x \<^bsub>/F\<^esub> the (\<Gamma> c) sat [p,R, G, q,a])"
  then have a1': "c \<in> dom \<Gamma>"  and       
       a1'': "\<Gamma>,\<Theta> \<union> Specs \<Turnstile>n \<^bsub>/F\<^esub> the (\<Gamma> c) sat [p,R, G, q,a]" using a0 by auto 
    from a1 have 
      valid_body:
      "\<forall>(c, p, R, G, q, a)\<in>Specs.
       c \<in> dom \<Gamma> \<and>  Sta p R \<and>   (\<forall>s. (Normal s,Normal s) \<in> G) \<and>    
       (\<forall>x. \<Gamma>,\<Theta> \<union> Specs \<Turnstile>x \<^bsub>/F\<^esub> the (\<Gamma> c) sat [p,R, G, q,a])" by fastforce
  assume a5: "Sta p R" and
         a6: "(\<forall>s. (Normal s,Normal s) \<in> G)" 
  obtain bdy where \<Gamma>bdy:"\<Gamma> c = Some bdy" using a1' by auto
  have theta_specs: 
         "\<forall>(c, p, R, G, q, a)\<in>\<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a] \<Longrightarrow>
          \<forall>(c, p, R, G, q, a)\<in>Specs. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]"
  proof(induct n)
    case 0    
    show "\<forall>(c, p, R, G, a, d)\<in>Specs. \<Gamma> \<Turnstile>0\<^bsub>/F\<^esub> LanguageCon.com.Call c sat [p,R, G, a,d]"
    proof-
      {fix c p R G a d
        assume a00:"(c, p, R, G, a, d) \<in> Specs"
        then have "c\<in>dom \<Gamma> \<and> Sta p R" using a1 by auto
        then have " \<Gamma> \<Turnstile>0\<^bsub>/F\<^esub> (LanguageCon.com.Call c) sat [p,R, G, a,d]"
          using not_val_zero  by fastforce
      } then show ?thesis by auto 
    qed       
  next
    case (Suc n)
    have hyp:"\<forall>(c, p, R, G, q, a)\<in>\<Theta>.  \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a] \<Longrightarrow>
             \<forall>(c, p, R, G, q, a)\<in>Specs. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]" by fact
    have body:"\<forall>(c, p, R, G, q, a)\<in>\<Theta>.  \<Gamma> \<Turnstile>Suc n\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]" by fact
    then show ?case
    proof-
      { fix c p R G q a
        assume a000:"(c, p, R, G, q, a) \<in> Specs"
        have ctxt_m:"\<forall>(c, p, R, G, q, a)\<in>\<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]"
          using body  cptn_mod_nest_mono  unfolding com_validityn_def cpn_def
          by (fastforce simp add: cpn_rule)
        then have valid_Proc:"\<forall>(c, p, R, G, q, a)\<in>Specs. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]"
          using hyp by auto
        have Sta:"Sta p R" using a1 a000 by auto
        have c_dom:" c \<in> dom \<Gamma>" using a1 a000 by auto
        have guar:"\<forall>s. (Normal s,Normal s)\<in>G" using a1 a000 by auto
        let ?\<Theta>'= "\<Theta> \<union> Specs"
        from valid_Proc ctxt_m
        have "\<forall>(c, p, R, G, q, a)\<in>?\<Theta>'. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]"
          by fastforce
        with valid_body
        have valid_body_m: 
          "\<forall>(c, p, R, G, q, a)\<in>Specs. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (the (\<Gamma> c)) sat [p,R, G, q,a]"
          by (fastforce  simp:com_cvalidityn_def)    
        then have valid_body:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (the (\<Gamma> c)) sat [p,R, G, q,a]" using a000 by auto
        then have "\<Gamma> \<Turnstile>Suc n\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]"
        proof-
        { fix l s 
          assume a01:"(\<Gamma>,l)\<in>cpn (Suc n) \<Gamma> (Call c) s \<and> (\<Gamma>,l)\<in> assum(p, R)"
          then have "length l \<ge> 1" unfolding cpn_def using CptnEmpty
            by (metis (no_types, lifting) One_nat_def Product_Type.Collect_case_prodD Suc_leI length_greater_0_conv snd_conv)
          moreover {
            assume a02:"length l = 1"
            then have "l = [(Call c,s)]" 
            proof -
              have "l ! 0 = (LanguageCon.com.Call c, s)" using a01 unfolding cpn_def
                by fastforce
              then show ?thesis using a02
                by (metis One_nat_def Suc_leI impossible_Cons 
                     length_greater_0_conv list.size(3) neq_Nil_conv nth_Cons_0 zero_neq_one) 
            qed 
            then have "(\<Gamma>,l) \<in> comm(G, (q,a)) F" unfolding comm_def final_def by auto
          }
          moreover {assume a02:"length l > 1"
            then obtain a1 ls where l:"l =(Call c, s)#a1#ls" using a01 unfolding cpn_def
              apply auto
              by (metis (no_types, hide_lams) One_nat_def Suc_eq_plus1 less_not_refl list.exhaust list.size(3) list.size(4) not_less_zero nth_Cons_0 prod.collapse)   
            have l_cptn:"(\<Gamma>,l)\<in>cptn" using a01 unfolding cpn_def
              using cptn_eq_cptn_mod_nest by blast
            then obtain m where min_call:"min_call m \<Gamma> l"
              using cptn_eq_cptn_mod_set cptn_mod_cptn_mod_nest minimum_nest_call by blast
            { assume a03:"\<forall>i<length l. fst (l!i) = Call c"     
              then have "(\<Gamma>,l) \<in> comm(G, (q,a)) F" 
                using no_comp_tran_no_final_comm[OF _ a03] a02 unfolding final_def
                by fastforce 
            }                                     
            moreover{
              assume a03:"\<not>(\<forall>i<length l. fst (l!i) = Call c)"
              then obtain i where i:"(i<length l \<and> fst (l!i) \<noteq> Call c)"
                by auto
              then obtain j where cfg_j:"fst (l!j) \<noteq> Call c \<and> (\<forall>k<j. fst (l!k) = Call c)"                     
                by (fast dest: exists_first_occ[of "\<lambda>i. fst (l!i) \<noteq> Call c" i])
              moreover have j:"j>0 \<and> j<length l" using l i calculation
                by (metis gr0I fstI leI le_less_trans nth_Cons') 
              ultimately have step:"(\<Gamma>\<turnstile>\<^sub>c (l!(j-1)) \<rightarrow> (l!j))"
                using l l_cptn
                by (metis One_nat_def Suc_pred cptn_stepc_rtran diff_less not_eq_not_env prod.collapse 
                   step_ce_elim_cases zero_less_one)
              then obtain s' where j_1_cfg:"snd (l!(j-1)) = Normal s' \<and> s' \<in> p"
                using cfg_j l a01[simplified l] j[simplified l] i Sta events_p[OF l_cptn[simplified l] _ _ _ Sta, of "j-1"]
                by force
              then have j_cfg:"l!j = (the (\<Gamma> c), Normal s')" 
                using cfg_j c_dom stepc_Normal_elim_cases(9) step
                by (metis diff_less domIff j option.sel prod.collapse zero_less_one)  
              then have suc_n_call:"(Suc n,\<Gamma>, drop (j-1) l) \<in> cptn_mod_nest_call" 
                using a01 unfolding cpn_def
                by (simp add: dropcptn_is_cptn1 j less_imp_diff_less)
              have "(n,\<Gamma>, drop j l) \<in> cptn_mod_nest_call" 
              proof-
                have "\<not> (\<Gamma>\<turnstile>\<^sub>c (l!(j-1)) \<rightarrow>\<^sub>e (l!j))" using step
                  by (metis etranE mod_env_not_component)
                then have "(Suc n,\<Gamma>, (Call c, Normal s')#(the (\<Gamma> c),Normal s')#(drop (j+1) l)) \<in> cptn_mod_nest_call"
                  using a01 j step cfg_j j_cfg j_1_cfg  suc_n_call
                  by (metis (no_types, lifting) Cons_nth_drop_Suc One_nat_def Suc_eq_plus1 
                    Suc_less_eq Suc_pred diff_less less_SucI prod.collapse zero_less_one)                  
                then have "(n,\<Gamma>, (the (\<Gamma> c),Normal s')#(drop (j+1) l)) \<in> cptn_mod_nest_call"
                  using cfg_j j_cfg  elim_cptn_mod_nest_call_n_dec[OF _ ] c_dom by fastforce
                then show ?thesis
                  by (metis Cons_nth_drop_Suc Suc_eq_plus1 j j_cfg)
              qed
              moreover have "(\<Gamma>, drop j l) \<in> assum(p,R)" 
              proof-   
                have "(\<Gamma>, take j l @ l ! j # drop (Suc j) l) \<in> assum (p, R)"
                  using conjunct2[OF a01] id_take_nth_drop[OF conjunct2[OF j]] by auto                             
                then show ?thesis 
                  using sub_assum_r[OF ]  j_1_cfg l j_cfg j
                  by (metis Cons_nth_drop_Suc image_eqI snd_conv)                  
              qed                              
              ultimately have comm_drop:"(\<Gamma>, drop j l)\<in> comm(G, (q,a)) F"
                using valid_body j_cfg j unfolding com_validityn_def cpn_def 
                by fastforce
              have "(\<Gamma>,l) \<in> comm(G, (q,a)) F" 
              proof-
                have h:"\<forall>j<length (take j l). fst ((take j l)!j) = (Call c)" using j cfg_j by fastforce
                then have comm_take:"(\<Gamma>,take j l) \<in> comm(G, (q,a)) F"
                  using no_comp_tran_no_final_comm[of "take j l" "Call c"] j_1_cfg l j_cfg j cfg_j 
                  unfolding final_def by auto                
                moreover have "(snd (last (take j l)), snd (drop j l ! 0)) \<in> G"
                proof-
                  have "length (take j l) = j"using l j_1_cfg j j_cfg by auto
                  moreover have "(take j l)!(j-1) = l!(j-1)"
                    using l j_1_cfg j j_cfg by auto
                  ultimately have "last (take j l) = l!(j-1)"
                    using  j by (metis last_conv_nth less_numeral_extra(3) list.size(3)) 
                  then  show ?thesis using l j_1_cfg j j_cfg guar by auto
                qed                                 
                ultimately show ?thesis using  j_1_cfg j_cfg j cfg_j j l_cptn
                  comm_union[OF comm_take comm_drop] by fastforce
              qed                 
             } ultimately have "(\<Gamma>,l)\<in>comm(G, (q,a)) F" by auto
           }ultimately  have "(\<Gamma>,l)\<in>comm(G, (q,a)) F" by fastforce         
         } thus ?thesis unfolding com_validityn_def using cpn_rule2 by blast 
       qed
      } thus ?case by fastforce
    qed
  qed 
  then show ?thesis using a0 unfolding com_cvalidityn_def by auto     
qed

lemma Seq_env_P:assumes a0:"\<Gamma>\<turnstile>\<^sub>c(Seq P Q,s) \<rightarrow>\<^sub>e (Seq P Q,t)"
      shows "\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow>\<^sub>e (P,t)"
using a0
by (metis env_not_normal_s snormal_enviroment)

lemma map_eq_state:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Seq c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift c2) l2"
shows
  "\<forall>i<length l1. snd (l1!i) = snd (l2!i)"
using a0 a1 a2 unfolding cp_def
by (simp add: snd_lift) 

lemma map_eq_seq_c:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Seq c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift c2) l2"
shows
  "\<forall>i<length l1. fst (l1!i) = Seq (fst (l2!i)) c2"
proof -
  {fix i
  assume a3:"i<length l1"
  have "fst (l1!i) = Seq (fst (l2!i)) c2"
  using a0 a1 a2 a3 unfolding lift_def
    by (simp add: case_prod_unfold) 
  }thus ?thesis by auto
qed 

lemma same_env_seq_c:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Seq c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift c2) l2"
shows
"\<forall>i. Suc i<length l2 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l2!i)  \<rightarrow>\<^sub>e (l2!(Suc i)) = 
            \<Gamma>\<turnstile>\<^sub>c(l1!i)  \<rightarrow>\<^sub>e (l1!(Suc i))" 
proof -
  have a0a:"(\<Gamma>,l1) \<in>cptn \<and> l1!0 = ((Seq c1 c2),s)" 
    using a0 unfolding cp_def by blast
  have a1a: "(\<Gamma>,l2) \<in>cptn \<and> l2!0 = (c1,s)"
    using a1 unfolding cp_def by blast
  {
    fix i
    assume a3:"Suc i< length l2"
    have "\<Gamma>\<turnstile>\<^sub>c(l2!i)  \<rightarrow>\<^sub>e (l2!(Suc i)) = 
            \<Gamma>\<turnstile>\<^sub>c(l1!i)  \<rightarrow>\<^sub>e (l1!(Suc i))"
    proof
    {
      assume a4:"\<Gamma>\<turnstile>\<^sub>c l2 ! i \<rightarrow>\<^sub>e l2 ! Suc i"
      obtain c1i s1i c1si s1si where l1prod:"l1 ! i=(c1i,s1i) \<and> l1!Suc i = (c1si,s1si)"
        by fastforce
      obtain c2i s2i c2si s2si where l2prod:"l2 ! i=(c2i,s2i) \<and> l2!Suc i = (c2si,s2si)"
        by fastforce
      then have "c1i = (Seq c2i c2) \<and> c1si = (Seq c2si c2)"
        using  a0 a1 a2 a3 a4  map_eq_seq_c l1prod
        by (metis Suc_lessD  fst_conv length_map)
      also have "s2i=s1i \<and> s2si=s1si"
        using  a0 a1 a4  a2 a3 l2prod map_eq_state l1prod
        by (metis Suc_lessD  nth_map snd_conv snd_lift)        
      ultimately show "\<Gamma>\<turnstile>\<^sub>c l1 ! i \<rightarrow>\<^sub>e (l1 ! Suc i)" 
        using a4 l1prod l2prod
        by (metis Env_n env_c_c' env_not_normal_s step_e.Env)
    } 
    {
      assume a4:"\<Gamma>\<turnstile>\<^sub>c l1 ! i \<rightarrow>\<^sub>e l1 ! Suc i"
      obtain c1i s1i c1si s1si where l1prod:"l1 ! i=(c1i,s1i) \<and> l1!Suc i = (c1si,s1si)"
        by fastforce
      obtain c2i s2i c2si s2si where l2prod:"l2 ! i=(c2i,s2i) \<and> l2!Suc i = (c2si,s2si)"
        by fastforce
      then have "c1i = (Seq c2i c2) \<and> c1si = (Seq c2si c2)"
        using  a0 a1 a2 a3 a4  map_eq_seq_c l1prod
        by (metis Suc_lessD  fst_conv length_map)
      also have "s2i=s1i \<and> s2si=s1si"
        using  a0 a1 a4  a2 a3 l2prod map_eq_state l1prod
        by (metis Suc_lessD  nth_map snd_conv snd_lift)        
      ultimately show "\<Gamma>\<turnstile>\<^sub>c l2 ! i \<rightarrow>\<^sub>e (l2 ! Suc i)" 
        using a4 l1prod l2prod        
        by (metis Env_n LanguageCon.com.inject(3) env_c_c' env_not_normal_s step_e.Env)   
    }
    qed
   } 
  thus ?thesis by auto
qed



lemma same_comp_seq_c:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Seq c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift c2) l2"
shows
"\<forall>i. Suc i<length l2 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l2!i)  \<rightarrow> (l2!(Suc i)) = 
            \<Gamma>\<turnstile>\<^sub>c(l1!i)  \<rightarrow> (l1!(Suc i))" 
proof -
  have a0a:"(\<Gamma>,l1) \<in>cptn \<and> l1!0 = ((Seq c1 c2),s)" 
    using a0 unfolding cp_def by blast
  have a1a: "(\<Gamma>,l2) \<in>cptn \<and> l2!0 = (c1,s)"
    using a1 unfolding cp_def by blast
  {
    fix i
    assume a3:"Suc i< length l2"
    have "\<Gamma>\<turnstile>\<^sub>c(l2!i)  \<rightarrow> (l2!(Suc i)) = 
            \<Gamma>\<turnstile>\<^sub>c(l1!i)  \<rightarrow> (l1!(Suc i))"
    proof
    {
      assume a4:"\<Gamma>\<turnstile>\<^sub>c l2 ! i \<rightarrow> l2 ! Suc i"
      obtain c1i s1i c1si s1si where l1prod:"l1 ! i=(c1i,s1i) \<and> l1!Suc i = (c1si,s1si)"
        by fastforce
      obtain c2i s2i c2si s2si where l2prod:"l2 ! i=(c2i,s2i) \<and> l2!Suc i = (c2si,s2si)"
        by fastforce
      then have "c1i = (Seq c2i c2) \<and> c1si = (Seq c2si c2)"
        using  a0 a1 a2 a3 a4  map_eq_seq_c l1prod
        by (metis Suc_lessD  fst_conv length_map)
      also have "s2i=s1i \<and> s2si=s1si"
        using  a0 a1 a4  a2 a3 l2prod map_eq_state l1prod
        by (metis Suc_lessD  nth_map snd_conv snd_lift)        
      ultimately show "\<Gamma>\<turnstile>\<^sub>c l1 ! i \<rightarrow> (l1 ! Suc i)" 
        using a4 l1prod l2prod
        by (simp add: Seqc)        
    } 
    {
      assume a4:"\<Gamma>\<turnstile>\<^sub>c l1 ! i \<rightarrow> l1 ! Suc i"
      obtain c1i s1i c1si s1si where l1prod:"l1 ! i=(c1i,s1i) \<and> l1!Suc i = (c1si,s1si)"
        by fastforce
      obtain c2i s2i c2si s2si where l2prod:"l2 ! i=(c2i,s2i) \<and> l2!Suc i = (c2si,s2si)"
        by fastforce
      then have "c1i = (Seq c2i c2) \<and> c1si = (Seq c2si c2)"
        using  a0 a1 a2 a3 a4  map_eq_seq_c l1prod
        by (metis Suc_lessD  fst_conv length_map)
      also have "s2i=s1i \<and> s2si=s1si"
        using  a0 a1 a4  a2 a3 l2prod map_eq_state l1prod
        by (metis Suc_lessD  nth_map snd_conv snd_lift)        
      ultimately show "\<Gamma>\<turnstile>\<^sub>c l2 ! i \<rightarrow> (l2 ! Suc i)" 
        using a4 l1prod l2prod stepc_elim_cases_Seq_Seq
      by auto           
    }
    qed
   } 
  thus ?thesis by auto
qed

lemma assum_map:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Seq c1 c2) s) \<and> ((\<Gamma>,l1) \<in> assum(p, R))" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift c2) l2"  
shows
  "((\<Gamma>,l2) \<in> assum(p, R))"
proof -
  have a3: "\<forall>i. Suc i<length l2 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l2!i)  \<rightarrow>\<^sub>e (l2!(Suc i)) = 
            \<Gamma>\<turnstile>\<^sub>c(l1!i)  \<rightarrow>\<^sub>e (l1!(Suc i))" 
    using a0 a1 a2 same_env_seq_c by fastforce
  have pair_\<Gamma>l1:"fst (\<Gamma>,l1) = \<Gamma> \<and> snd (\<Gamma>,l1) = l1" by fastforce
  have pair_\<Gamma>l2:"fst (\<Gamma>,l2) = \<Gamma> \<and> snd (\<Gamma>,l2) = l2" by fastforce
  have drop_k_s:"l2!0 = (c1,s)" using a1 cp_def by blast
  have eq_length:"length l1 = length l2" using a2 by auto
  obtain s' where normal_s:"s = Normal s'" 
    using  a0  unfolding cp_def   assum_def  by fastforce
  then have p1:"s'\<in>p" using a0 unfolding cp_def assum_def by fastforce  
  show ?thesis 
  proof -    
    let ?c= "(\<Gamma>,l2)"
    have l:"snd((snd ?c!0)) \<in> Normal ` (p)"
     using p1 drop_k_s a1 normal_s unfolding cp_def by auto
    {fix i
     assume a00:"Suc i<length (snd ?c)" 
     assume a11:"(fst ?c)\<turnstile>\<^sub>c((snd ?c)!i)  \<rightarrow>\<^sub>e ((snd ?c)!(Suc i))"
     have "(snd((snd ?c)!i), snd((snd ?c)!(Suc i))) \<in> R"
     using a0 a1 a2 a3 map_eq_state unfolding assum_def 
     using a00 a11 eq_length by fastforce
    } thus "(\<Gamma>, l2) \<in> assum (p, R)" 
      using l unfolding assum_def by fastforce  
  qed  
qed

lemma comm_map':
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Seq c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) \<and> (\<Gamma>, l2)\<in> comm(G, (q,a)) F" and
  a2:"l1=map (lift c2) l2" 
shows
  "snd (last l1) \<notin> Fault ` F  \<longrightarrow>(Suc k < length l1 \<longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c(l1!k)  \<rightarrow> (l1!(Suc k)) \<longrightarrow> 
       (snd(l1!k), snd(l1!(Suc k))) \<in>  G) \<and> 
   (fst (last l1) = (Seq c c2) \<and> final (c, snd (last l1)) \<longrightarrow>     
      (fst (last l1) = (Seq Skip c2) \<and> 
        (snd (last  l1) \<in> Normal ` q) \<or>
      (fst (last l1) = (Seq Throw c2) \<and> 
        snd (last l1) \<in> Normal ` (a))))
     "
proof -
  have a3:"\<forall>i. Suc i<length l2 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l2!i)  \<rightarrow> (l2!(Suc i)) = 
            \<Gamma>\<turnstile>\<^sub>c(l1!i)  \<rightarrow> (l1!(Suc i))" 
    using a0 a1 a2 same_comp_seq_c
    by fastforce
  have pair_\<Gamma>l1:"fst (\<Gamma>,l1) = \<Gamma> \<and> snd (\<Gamma>,l1) = l1" by fastforce
  have pair_\<Gamma>l2:"fst (\<Gamma>,l2) = \<Gamma> \<and> snd (\<Gamma>,l2) = l2" by fastforce
  have drop_k_s:"l2!0 = (c1,s)" using a1 cp_def by blast
  have eq_length:"length l1 = length l2" using a2 by auto 
  then have len0:"length l1>0" using a0 unfolding cp_def 
    using Collect_case_prodD drop_k_s eq_length by auto
  then have l1_not_empty:"l1\<noteq>[]" by auto
  then have l2_not_empty:"l2 \<noteq> []" using a2 by blast       
   have last_lenl1:"last l1 = l1!((length l1) -1)" 
        using last_conv_nth l1_not_empty by auto
  have last_lenl2:"last l2 = l2!((length l2) -1)" 
       using last_conv_nth l2_not_empty by auto 
  have a03:"snd (last l2) \<notin> Fault ` F  \<longrightarrow>(\<forall>i ns ns'.                 
               Suc i<length (snd (\<Gamma>, l2)) \<longrightarrow> 
               fst (\<Gamma>, l2)\<turnstile>\<^sub>c((snd (\<Gamma>, l2))!i)  \<rightarrow> ((snd (\<Gamma>, l2))!(Suc i)) \<longrightarrow>                               
                 (snd((snd (\<Gamma>, l2))!i), snd((snd (\<Gamma>, l2))!(Suc i))) \<in> G) \<and> 
               (final (last (snd (\<Gamma>, l2)))  \<longrightarrow>                 
                  ((fst (last (snd (\<Gamma>, l2))) = Skip \<and> 
                    snd (last (snd (\<Gamma>, l2))) \<in> Normal ` q)) \<or>
                  (fst (last (snd (\<Gamma>, l2))) = Throw \<and> 
                    snd (last (snd (\<Gamma>, l2))) \<in> Normal ` (a)))"
  using a1 unfolding comm_def by fastforce
  show ?thesis unfolding comm_def 
  proof -
  { fix k ns ns'
    assume a00a:"snd (last l1) \<notin> Fault ` F"
    assume a00:"Suc k < length l1"    
    then have "k \<le> length l1" using a2 by fastforce    
    have a00:"Suc k < length l2" using eq_length a00 by fastforce
    then have a00a:"snd (last l2) \<notin> Fault ` F"
    proof-
      have "snd (l1!((length l1) -1)) = snd (l2!((length l2) -1))"      
        using a2 a1 a0  map_eq_state eq_length l2_not_empty last_snd 
        by fastforce 
      then have "snd(last l2) = snd (last l1)"
        using last_lenl1 last_lenl2 by auto
      thus ?thesis using a00a by auto
    qed
    then have "snd (last l1) \<notin> Fault ` F \<longrightarrow>\<Gamma>\<turnstile>\<^sub>c(l1!k)  \<rightarrow> (l1!(Suc k)) \<longrightarrow>       
      (snd((snd (\<Gamma>, l1))!k), snd((snd (\<Gamma>, l1))!(Suc k))) \<in>  G"
    using  pair_\<Gamma>l1 pair_\<Gamma>l2 a00  a03 a3  eq_length a00a
     by (metis Suc_lessD a0 a1 a2 map_eq_state)
  } note l=this
  {
    assume a00: "fst (last l1) = (Seq c c2) \<and> final (c, snd (last l1))" and
           a01:"snd (last (l1)) \<notin> Fault ` F"
    then have c:"c=Skip \<or> c = Throw"
     unfolding final_def by auto    
    then have fst_last_l2:"fst (last l2) = c"                               
      using  last_lenl1 a00 l1_not_empty eq_length len0 a2 last_conv_nth last_lift 
      by fastforce      
    also have last_eq:"snd (last l2) = snd (last l1)"      
      using l2_not_empty a2 last_conv_nth last_lenl1 last_snd 
      by fastforce
    ultimately have "final (fst (last l2),snd (last l2))" 
     using a00 by auto
    then have "final (last l2)" by auto
    also have "snd (last (l2)) \<notin> Fault ` F"
       using  last_eq a01 by auto
    ultimately have "(fst (last  l2)) = Skip \<and> 
                    snd (last  l2) \<in> Normal ` q \<or>
                  (fst (last l2) = Throw \<and> 
                    snd (last l2) \<in> Normal ` (a))"
    using a03 by auto
    then have "(fst (last l1) = (Seq Skip c2) \<and> 
                    snd (last  l1) \<in> Normal ` q) \<or>
                  (fst (last l1) = (Seq Throw c2) \<and> 
                    snd (last l1) \<in> Normal ` (a))"
    using last_eq fst_last_l2 a00 by force
  }
  thus ?thesis using l by auto qed
qed

lemma comm_map'':
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Seq c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) \<and> (\<Gamma>, l2)\<in> comm(G, (q,a)) F" and
  a2:"l1=map (lift c2) l2" 
shows
  "snd (last l1) \<notin> Fault ` F \<longrightarrow> ((Suc k < length l1 \<longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c(l1!k)  \<rightarrow> (l1!(Suc k)) \<longrightarrow>        
       (snd(l1!k), snd(l1!(Suc k))) \<in> G) \<and> 
   (final (last l1) \<longrightarrow>     
      (fst (last l1) = Skip \<and> 
        (snd (last  l1) \<in> Normal ` r) \<or>
      (fst (last l1) = Throw \<and> 
        snd (last l1) \<in> Normal ` (a)))))
     "
proof -
  have a3:"\<forall>i. Suc i<length l2 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l2!i)  \<rightarrow> (l2!(Suc i)) = 
            \<Gamma>\<turnstile>\<^sub>c(l1!i)  \<rightarrow> (l1!(Suc i))" 
    using a0 a1 a2 same_comp_seq_c
    by fastforce
  have pair_\<Gamma>l1:"fst (\<Gamma>,l1) = \<Gamma> \<and> snd (\<Gamma>,l1) = l1" by fastforce
  have pair_\<Gamma>l2:"fst (\<Gamma>,l2) = \<Gamma> \<and> snd (\<Gamma>,l2) = l2" by fastforce
  have drop_k_s:"l2!0 = (c1,s)" using a1 cp_def by blast
  have eq_length:"length l1 = length l2" using a2 by auto 
  then have len0:"length l1>0" using a0 unfolding cp_def 
    using Collect_case_prodD drop_k_s eq_length by auto
  then have l1_not_empty:"l1\<noteq>[]" by auto
  then have l2_not_empty:"l2 \<noteq> []" using a2 by blast       
  have last_lenl1:"last l1 = l1!((length l1) -1)" 
        using last_conv_nth l1_not_empty by auto
  have last_lenl2:"last l2 = l2!((length l2) -1)" 
       using last_conv_nth l2_not_empty by auto 
  have a03:"snd (last l2) \<notin> Fault ` F \<longrightarrow>(\<forall>i ns ns'.                 
               Suc i<length (snd (\<Gamma>, l2)) \<longrightarrow> 
               fst (\<Gamma>, l2)\<turnstile>\<^sub>c((snd (\<Gamma>, l2))!i)  \<rightarrow> ((snd (\<Gamma>, l2))!(Suc i)) \<longrightarrow>                                            
                 (snd((snd (\<Gamma>, l2))!i), snd((snd (\<Gamma>, l2))!(Suc i))) \<in> G) \<and> 
               (final (last (snd (\<Gamma>, l2)))  \<longrightarrow>                 
                  ((fst (last (snd (\<Gamma>, l2))) = Skip \<and> 
                    snd (last (snd (\<Gamma>, l2))) \<in> Normal ` q)) \<or>
                  (fst (last (snd (\<Gamma>, l2))) = Throw \<and> 
                    snd (last (snd (\<Gamma>, l2))) \<in> Normal ` (a)))"
  using a1 unfolding comm_def by fastforce
  show ?thesis unfolding comm_def 
  proof -
  { fix k ns ns'
    assume a00a:"snd (last l1) \<notin> Fault ` F"
    assume a00:"Suc k < length l1"    
    then have "k \<le> length l1" using a2 by fastforce    
    have a00:"Suc k < length l2" using eq_length a00 by fastforce   
    then have a00a:"snd (last l2) \<notin> Fault ` F"
    proof-
      have "snd (l1!((length l1) -1)) = snd (l2!((length l2) -1))"      
        using a2 a1 a0  map_eq_state eq_length l2_not_empty last_snd 
        by fastforce 
      then have "snd(last l2) = snd (last l1)"
        using last_lenl1 last_lenl2 by auto
      thus ?thesis using a00a by auto
    qed 
    then have "\<Gamma>\<turnstile>\<^sub>c(l1!k)  \<rightarrow> (l1!(Suc k)) \<longrightarrow>         
        (snd((snd (\<Gamma>, l1))!k), snd((snd (\<Gamma>, l1))!(Suc k))) \<in> G"
       using  pair_\<Gamma>l1 pair_\<Gamma>l2 a00  a03 a3  eq_length a00a
      by (metis (no_types,lifting) a2 Suc_lessD nth_map snd_lift)
    } note l= this
    {
     assume a00: "final (last l1)"           
     then have c:"fst (last l1)=Skip \<or> fst (last l1) = Throw"
       unfolding final_def by auto 
     moreover have "fst (last l1) = Seq (fst (last l2)) c2" 
       using a2 last_lenl1 eq_length
      proof -
        have "last l2 = l2 ! (length l2 - 1)"
          using l2_not_empty last_conv_nth by blast
        then show ?thesis
          by (metis One_nat_def a2 l2_not_empty last_lenl1 last_lift)
      qed
      ultimately have False by simp  
    } thus ?thesis using l  by auto qed
qed

lemma comm_map:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Seq c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) \<and> (\<Gamma>, l2)\<in> comm(G, (q,a)) F" and
  a2:"l1=map (lift c2) l2" 
shows
  "(\<Gamma>, l1)\<in> comm(G, (r,a)) F"
proof - 
  {fix i 
   have "snd (last l1) \<notin> Fault ` F  \<longrightarrow>(Suc i < length (l1) \<longrightarrow>
        \<Gamma>\<turnstile>\<^sub>c (l1 ! i) \<rightarrow> (l1 ! (Suc i)) \<longrightarrow>       
        (snd (l1 ! i), snd (l1 ! Suc i)) \<in> G) \<and>
        (SmallStepCon.final (last l1) \<longrightarrow>                  
                   fst (last l1) = LanguageCon.com.Skip \<and>
                   snd (last l1) \<in> Normal ` r \<or>
                   fst (last l1) = LanguageCon.com.Throw \<and>
                   snd (last l1) \<in> Normal ` a) "
      using comm_map''[of \<Gamma> l1 c1 c2 s l2 G q a F i r] a0 a1 a2 
      by fastforce
   }  then show ?thesis using comm_def unfolding comm_def by force       
qed
(* declare[[show_types]]
lemma "(SOME e. e\<in>{1::nat,2,3}) = 1 \<or> (SOME e. e\<in>{1::nat,2,3}) = 2 \<or> (SOME e. e\<in>{1::nat,2,3}) = 3"
  apply auto
  by (metis (mono_tags, lifting) someI)*)


lemma Seq_sound1:
assumes
  a0:"(n,\<Gamma>,x)\<in>cptn_mod_nest_call" and
  a1:"x!0 = ((Seq P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"\<not> final (last x)" and
  a4:"env_tran_right \<Gamma> x rely" and
  a5:"snd (x!0)\<in> Normal ` p \<and> Sta p rely \<and> Sta a rely " and 
  a6: "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> P sat [p, rely, G, q,a]" 
shows
  "\<exists>xs. (\<Gamma>,xs) \<in> cpn n \<Gamma> P s \<and> x = map (lift Q) xs"
using a0 a1 a2 a3 a4  a5 a6
proof (induct arbitrary: P s p) 
  case (CptnModNestOne n \<Gamma> C s1)
  then have "(\<Gamma>, [(P,s)]) \<in> cpn n \<Gamma> P s \<and> [(C, s1)] = map (lift Q) [(P,s)]"
    unfolding cpn_def lift_def
    by (simp add: cptn_mod_nest_call.CptnModNestOne) 
  thus ?case by fastforce
next
  case (CptnModNestEnv \<Gamma> C s1 t1 n xsa)
  then have C:"C=Seq P Q" unfolding lift_def by fastforce
  have "\<exists>xs. (\<Gamma>, xs) \<in> cpn n \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift Q) xs"
  proof -
     have "((C, t1) # xsa) ! 0 = (LanguageCon.com.Seq P Q, t1)" using C by auto
     moreover have "\<forall>i<length ((C, t1) # xsa). fst (((C, t1) # xsa) ! i) \<noteq> Q"
       using CptnModNestEnv(5) by fastforce
     moreover have "\<not> SmallStepCon.final (last ((C, t1) # xsa))" using CptnModNestEnv(6) 
       by fastforce
     moreover have "snd (((C, t1) # xsa) ! 0) \<in> Normal ` p" 
       using CptnModNestEnv(8) CptnModNestEnv(1) CptnModNestEnv(7)
       unfolding env_tran_right_def Sta_def by fastforce 
     ultimately show ?thesis
       using CptnModNestEnv(3) CptnModNestEnv(7) CptnModNestEnv(8)  CptnModNestEnv(9) env_tran_tail by blast
  qed 
  then obtain xs where hi:"(\<Gamma>, xs) \<in> cpn n \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift Q) xs"
    by fastforce
  have s1_s:"s1=s" using  CptnModNestEnv unfolding cpn_def by auto
  obtain xsa' where xs:"xs=((P,t1)#xsa') \<and> (n, \<Gamma>,((P,t1)#xsa'))\<in>cptn_mod_nest_call \<and> (C, t1) # xsa = map (lift Q) ((P,t1)#xsa')" 
    using hi  unfolding cpn_def by fastforce  
  have env_tran:"\<Gamma>\<turnstile>\<^sub>c(P,s1) \<rightarrow>\<^sub>e (P,t1)" using CptnModNestEnv Seq_env_P by (metis fst_conv nth_Cons_0)  
  then have "(n, \<Gamma>,(P,s1)#(P,t1)#xsa')\<in>cptn_mod_nest_call" 
    using xs env_tran cptn_mod_nest_call.CptnModNestEnv by fastforce  
  then have "(\<Gamma>,(P,s1)#(P,t1)#xsa') \<in> cpn n \<Gamma> P s" 
    using cpn_def s1_s by fastforce
  moreover have "(C,s1)#(C, t1) # xsa = map (lift Q) ((P,s1)#(P,t1)#xsa')"
    using xs C unfolding lift_def by fastforce
  ultimately show ?case by auto
next
  case (CptnModNestSkip)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModNestThrow)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModNestSeq1 n \<Gamma> P0 sa xsa zs P1)
  then have a1:"LanguageCon.com.Seq P Q = LanguageCon.com.Seq P0 P1"
    by fastforce  
  have f1: "sa = s"
    using CptnModNestSeq1.prems(1) by force
  have f2: "P = P0 \<and> Q = P1" using a1 by auto  
  hence "(\<Gamma>, (P0, sa) # xsa) \<in> cpn n \<Gamma> P s"
    using f2 f1 CptnModNestSeq1.hyps(1) by (simp add: cpn_def)
  thus ?case
    using Cons_lift CptnModNestSeq1.hyps(3) a1 by fastforce   
next
  case (CptnModNestSeq2 n \<Gamma> P0 sa xsa P1 ys zs) 
  then have "P0 = P \<and> P1 = Q" by auto
  then obtain i where zs:"fst (zs!i) = Q \<and> (i< (length zs))" using CptnModNestSeq2
    by (metis (no_types, lifting) add_diff_cancel_left' fst_conv length_Cons length_append nth_append_length zero_less_Suc zero_less_diff)    
  then have "Suc i< length ((Seq P0 P1,sa)#zs)" by fastforce
  then have "fst (((Seq P0 P1, sa) # zs)!Suc i) = Q" using zs by fastforce    
  thus ?case using CptnModNestSeq2(8) zs by auto
next
  case (CptnModNestSeq3 n \<Gamma> P1 sa xsa s' ys zs Q1 )          
  have s'_a:"s' \<in>  a"   
  proof -
    have  cpP1:"(\<Gamma>, (P1, Normal sa) # xsa) \<in> cpn n \<Gamma> P1 (Normal sa)" 
      using CptnModNestSeq3.hyps(1)  unfolding cpn_def by fastforce
    then have  cpP1':"(\<Gamma>, (P1, Normal sa) # xsa) \<in> cp \<Gamma> P1 (Normal sa)"
      using CptnModNestSeq3.hyps(1)  cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod 
      unfolding cp_def by fastforce       
    have map:"((Seq P1 Q1), Normal sa)#(map (lift Q1) xsa) = map (lift Q1)  ((P1, Normal sa) # xsa) "
      using CptnModSeq3 by (simp add: Cons_lift) 
    then 
    have "(\<Gamma>,((LanguageCon.com.Seq P1 Q1, Normal sa) # (map (lift Q1) xsa))) \<in> assum (p,rely)"
    proof - 
      have "env_tran_right \<Gamma> ((LanguageCon.com.Seq P1 Q1, Normal sa) # (map (lift Q1) xsa)) rely" 
        using  CptnModNestSeq3(11) CptnModNestSeq3(7) map
        by (metis (no_types) Cons_lift_append CptnModNestSeq3.hyps(7) CptnModNestSeq3.prems(4) env_tran_subr) 
      thus ?thesis using CptnModNestSeq3(12) 
      unfolding assum_def env_tran_right_def by fastforce  
    qed
    moreover have "(\<Gamma>,((Seq P1 Q1), Normal sa)#(map (lift Q1) xsa)) \<in> cpn n \<Gamma> (Seq P1 Q1) (Normal sa)"
      using CptnModNestSeq3(7) CptnModNestSeq3.hyps(1)  cptn_mod_nest_call.CptnModNestSeq1
      unfolding cpn_def by fastforce  
    then have  "(\<Gamma>,((Seq P1 Q1), Normal sa)#(map (lift Q1) xsa)) \<in> cp \<Gamma> (Seq P1 Q1) (Normal sa)"
      using CptnModNestSeq3.hyps(1)  cptn_eq_cptn_mod_set cptn_mod.CptnModSeq1 cptn_mod_nest_cptn_mod 
      unfolding cp_def by fastforce      
    ultimately have  "(\<Gamma>, (P1, Normal sa) # xsa) \<in> assum (p,rely)" 
      using assum_map map cpP1' by fastforce
    then have "(\<Gamma>, (P1, Normal sa) # xsa) \<in> comm (G,(q,a)) F" 
      using cpP1 CptnModNestSeq3(13)  CptnModNestSeq3.prems(1) unfolding com_validityn_def by auto
    thus ?thesis   
      using CptnModNestSeq3(3)  CptnModNestSeq3(4)
      unfolding comm_def final_def by fastforce
  qed
  have "final (last ((LanguageCon.com.Throw, Normal s')# ys))"
  proof -
    have cptn_mod:"(n, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call" 
      using CptnModNestSeq3(5) by (simp add: cptn_eq_cptn_mod_set)
    then have cptn:"(\<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn"
      using cptn_eq_cptn_mod_nest by auto
    moreover have throw_0:"((LanguageCon.com.Throw, Normal s') # ys)!0 = (Throw, Normal s') \<and> 0 < length((LanguageCon.com.Throw, Normal s') # ys)"
      by force         
    moreover have last:"last ((LanguageCon.com.Throw, Normal s') # ys) = ((LanguageCon.com.Throw, Normal s') # ys)!((length ((LanguageCon.com.Throw, Normal s') # ys)) - 1)"
      using last_conv_nth by auto
    moreover have env_tran:"env_tran_right \<Gamma> ((LanguageCon.com.Throw, Normal s') # ys) rely" 
      using  CptnModNestSeq3(11)  CptnModNestSeq3(7) env_tran_subl env_tran_tail by blast           
    ultimately obtain st' where "fst (last ((LanguageCon.com.Throw, Normal s') # ys)) = Throw \<and>        
                     snd (last ((LanguageCon.com.Throw, Normal s') # ys)) = Normal st'" 
    using zero_throw_all_throw[of \<Gamma> "((Throw, Normal s') # ys)" "s'" "(length ((Throw, Normal s') # ys))-1" a rely]
          s'_a CptnModNestSeq3(11) CptnModNestSeq3(12) by fastforce      
    thus ?thesis using CptnModNestSeq3(10) final_def by blast
  qed
  thus ?case using CptnModNestSeq3(10) CptnModNestSeq3(7)
    by force
qed (auto)

lemma Seq_sound2: 
assumes
  a0:"(\<Gamma>,x)\<in>cptn_mod" and
  a1:"x!0 = ((Seq P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"fst (last x) = Throw \<and> snd (last x) = Normal s'" and
  a4:"env_tran_right \<Gamma> x rely"
shows
  "\<exists>xs s' ys. (\<Gamma>,xs) \<in> cp \<Gamma> P s \<and> x = ((map (lift Q) xs)@((Throw, Normal s')#ys))"
using a0 a1 a2 a3 a4
proof (induct arbitrary: P s s')
  case (CptnModOne \<Gamma> C s1)
  then have "(\<Gamma>, [(P,s)]) \<in> cp \<Gamma> P s \<and> [(C, s1)] = map (lift Q) [(P,s)]@[(Throw, Normal s')]"
    unfolding cp_def lift_def  by (simp add: cptn.CptnOne) 
  thus ?case by fastforce
next
  case (CptnModEnv \<Gamma> C s1 t1 xsa)
  then have C:"C=Seq P Q" unfolding lift_def by fastforce
  have "\<exists>xs s' ys. (\<Gamma>, xs) \<in> cp \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift Q) xs@((Throw, Normal s')#ys)"
  proof -
     have "((C, t1) # xsa) ! 0 = (LanguageCon.com.Seq P Q, t1)" using C by auto
     moreover have "\<forall>i<length ((C, t1) # xsa). fst (((C, t1) # xsa) ! i) \<noteq> Q"
       using CptnModEnv(5) by fastforce
     moreover have "fst (last ((C, t1) # xsa)) = Throw \<and> snd (last ((C, t1) # xsa)) = Normal s'" using CptnModEnv(6) 
       by fastforce
     ultimately show ?thesis
       using CptnModEnv(3) CptnModEnv(7) env_tran_tail by blast     
  qed 
  then obtain xs s'' ys where hi:"(\<Gamma>, xs) \<in> cp \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift Q) xs@((Throw, Normal s'')#ys)"
    by fastforce
  have s1_s:"s1=s" using  CptnModEnv unfolding cp_def by auto
  have "\<exists>xsa' s'' ys. xs=((P,t1)#xsa') \<and> (\<Gamma>,((P,t1)#xsa'))\<in>cptn \<and> (C, t1) # xsa = map (lift Q) ((P,t1)#xsa')@((Throw, Normal s'')#ys)" 
    using hi  unfolding cp_def
  proof -
      have "(\<Gamma>,xs)\<in>cptn \<and> xs!0 = (P,t1)" using hi unfolding cp_def by fastforce
      moreover then have "xs\<noteq>[]" using cptn.simps by fastforce  
      ultimately obtain xsa' where "xs=((P,t1)#xsa')" using SmallStepCon.nth_tl by fastforce 
      thus ?thesis
        using hi using \<open>(\<Gamma>, xs) \<in> cptn \<and> xs ! 0 = (P, t1)\<close> by auto 
  qed
  then obtain xsa' s'' ys where xs:"xs=((P,t1)#xsa') \<and> (\<Gamma>,((P,t1)#xsa'))\<in>cptn \<and> (C, t1) # xsa = map (lift Q) ((P,t1)#xsa')@((Throw, Normal s'')#ys)"
    by fastforce
  have env_tran:"\<Gamma>\<turnstile>\<^sub>c(P,s1) \<rightarrow>\<^sub>e (P,t1)" using CptnModEnv Seq_env_P by (metis fst_conv nth_Cons_0)  
  then have "(\<Gamma>,(P,s1)#(P,t1)#xsa')\<in>cptn" using xs env_tran CptnEnv by fastforce  
  then have "(\<Gamma>,(P,s1)#(P,t1)#xsa') \<in> cp \<Gamma> P s" 
    using cp_def s1_s by fastforce
  moreover have "(C,s1)#(C, t1) # xsa = map (lift Q) ((P,s1)#(P,t1)#xsa')@((Throw, Normal s'')#ys)"
    using xs C unfolding lift_def by fastforce
  ultimately show ?case by auto
next
  case (CptnModSkip)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModThrow)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModSeq1 \<Gamma> P0 sa xsa zs P1)  
  thus ?case    
  proof -
    have a1:"\<forall>c p. fst (case p of (ca::('s, 'a, 'd,'e) LanguageCon.com, x::('s, 'd) xstate) \<Rightarrow> 
                (LanguageCon.com.Seq ca c, x)) = LanguageCon.com.Seq (fst p) c"
      by simp
    then have "[] = xsa"     
    proof -
     have "[] \<noteq> zs"
       using CptnModSeq1 by force
     then show ?thesis
       by (metis (no_types) LanguageCon.com.distinct(71) One_nat_def CptnModSeq1(3,6) 
                            last.simps last_conv_nth last_lift)
    qed   
    then have "\<forall>c. Throw = c \<or> [] = zs"
      using CptnModSeq1(3) by fastforce
    then show ?thesis
      using CptnModSeq1.prems(3) by force
  qed   
next
  case (CptnModSeq2 \<Gamma> P0 sa xsa P1 ys zs) 
  then have "P0 = P \<and> P1 = Q" by auto
  then obtain i where zs:"fst (zs!i) = Q \<and> (i< (length zs))" using CptnModSeq2
    by (metis (no_types, lifting) add_diff_cancel_left' fst_conv length_Cons length_append nth_append_length zero_less_Suc zero_less_diff)    
  then have "Suc i< length ((Seq P0 P1,sa)#zs)" by fastforce
  then have "fst (((Seq P0 P1, sa) # zs)!Suc i) = Q" using zs by fastforce    
  thus ?case using CptnModSeq2(8) zs by auto
next 
  case (CptnModSeq3 \<Gamma> P0 sa xsa s'' ys zs P1)  
  then have "P0 = P \<and> P1 = Q \<and> s=Normal sa" by auto  
  moreover then have "(\<Gamma>, (P0, Normal sa) # xsa)\<in> cp \<Gamma> P s" 
    using CptnModSeq3(1)
    by (simp add: cp_def cptn_eq_cptn_mod_set)  
  moreover have "last zs=(Throw, Normal s')" using CptnModSeq3(10) CptnModSeq3.hyps(7) 
    by (simp add: prod_eqI)    
  ultimately show ?case using  CptnModSeq3(7)
    using Cons_lift_append by blast      
qed (auto)


lemma Seq_sound2': 
assumes
  a0:"(n,\<Gamma>,x)\<in>cptn_mod_nest_call" and
  a1:"x!0 = ((Seq P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"fst (last x) = Throw \<and> snd (last x) = Normal s'" and
  a4:"env_tran_right \<Gamma> x rely"
shows
  "\<exists>xs s' ys. (\<Gamma>,xs) \<in> cpn n \<Gamma> P s \<and> x = ((map (lift Q) xs)@((Throw, Normal s')#ys))"
using a0 a1 a2 a3 a4
proof (induct arbitrary: P s s')
  case (CptnModNestOne n \<Gamma> C s1)
  then have "(\<Gamma>, [(P,s)]) \<in> cpn n \<Gamma> P s \<and> [(C, s1)] = map (lift Q) [(P,s)]@[(Throw, Normal s')]"
    unfolding cp_def lift_def  by (simp add: cptn.CptnOne) 
  thus ?case by fastforce
next
  case (CptnModNestEnv \<Gamma> C s1 t1 n xsa)
  then have C:"C=Seq P Q" unfolding lift_def by fastforce
  have "\<exists>xs s' ys. (\<Gamma>, xs) \<in> cpn n \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift Q) xs@((Throw, Normal s')#ys)"
  proof -
     have "((C, t1) # xsa) ! 0 = (LanguageCon.com.Seq P Q, t1)" using C by auto
     moreover have "\<forall>i<length ((C, t1) # xsa). fst (((C, t1) # xsa) ! i) \<noteq> Q"
       using CptnModNestEnv(5) by fastforce
     moreover have "fst (last ((C, t1) # xsa)) = Throw \<and> snd (last ((C, t1) # xsa)) = Normal s'" 
       using CptnModNestEnv(6) 
       by fastforce
     ultimately show ?thesis
       using CptnModNestEnv(3) CptnModNestEnv(7) env_tran_tail by blast     
  qed 
  then obtain xs s'' ys where hi:"(\<Gamma>, xs) \<in> cpn n \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift Q) xs@((Throw, Normal s'')#ys)"
    by fastforce
  have s1_s:"s1=s" using  CptnModNestEnv unfolding cp_def by auto
  have "\<exists>xsa' s'' ys. xs=((P,t1)#xsa') \<and> (n, \<Gamma>,((P,t1)#xsa'))\<in>cptn_mod_nest_call \<and> (C, t1) # xsa = map (lift Q) ((P,t1)#xsa')@((Throw, Normal s'')#ys)" 
    using hi  unfolding cp_def
  proof -
      have "(n, \<Gamma>,xs)\<in>cptn_mod_nest_call \<and> xs!0 = (P,t1)" using hi unfolding cpn_def by fastforce
      moreover then have "xs\<noteq>[]" using cptn_mod_nest_call.simps by fastforce  
      ultimately obtain xsa' where "xs=((P,t1)#xsa')" using SmallStepCon.nth_tl by fastforce 
      thus ?thesis
        using hi using \<open>(n, \<Gamma>, xs) \<in> cptn_mod_nest_call \<and> xs ! 0 = (P, t1)\<close> by auto 
  qed
  then obtain xsa' s'' ys where xs:"xs=((P,t1)#xsa') \<and> (n, \<Gamma>,((P,t1)#xsa'))\<in>cptn_mod_nest_call \<and> 
                (C, t1) # xsa = map (lift Q) ((P,t1)#xsa')@((Throw, Normal s'')#ys)"
    by fastforce
  have env_tran:"\<Gamma>\<turnstile>\<^sub>c(P,s1) \<rightarrow>\<^sub>e (P,t1)" using CptnModNestEnv Seq_env_P by (metis fst_conv nth_Cons_0)  
  then have "(n, \<Gamma>,(P,s1)#(P,t1)#xsa')\<in>cptn_mod_nest_call" using xs env_tran cptn_mod_nest_call.CptnModNestEnv by blast    
  then have "(\<Gamma>,(P,s1)#(P,t1)#xsa') \<in> cpn n \<Gamma> P s" 
    using cpn_def s1_s by fastforce
  moreover have "(C,s1)#(C, t1) # xsa = map (lift Q) ((P,s1)#(P,t1)#xsa')@((Throw, Normal s'')#ys)"
    using xs C unfolding lift_def by fastforce
  ultimately show ?case by auto
next
  case (CptnModNestSkip)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModNestThrow)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModNestSeq1 n \<Gamma> P0 sa xsa zs P1)  
  thus ?case    
  proof -
    have a1:"\<forall>c p. fst (case p of (ca::('s, 'a, 'd,'e) LanguageCon.com, x::('s, 'd) xstate) \<Rightarrow> 
                (LanguageCon.com.Seq ca c, x)) = LanguageCon.com.Seq (fst p) c"
      by simp
    then have "[] = xsa"     
    proof -
     have "[] \<noteq> zs"
       using CptnModNestSeq1 by force
     then show ?thesis
       by (metis (no_types) LanguageCon.com.distinct(71) One_nat_def CptnModNestSeq1(3,6) 
                            last.simps last_conv_nth last_lift)
    qed   
    then have "\<forall>c. Throw = c \<or> [] = zs"
      using CptnModNestSeq1(3) by fastforce
    then show ?thesis
      using CptnModNestSeq1.prems(3) by force
  qed   
next
  case (CptnModNestSeq2 n \<Gamma> P0 sa xsa P1 ys zs) 
  then have "P0 = P \<and> P1 = Q" by auto
  then obtain i where zs:"fst (zs!i) = Q \<and> (i< (length zs))" using CptnModNestSeq2
    by (metis (no_types, lifting) add_diff_cancel_left' fst_conv length_Cons length_append nth_append_length zero_less_Suc zero_less_diff)    
  then have "Suc i< length ((Seq P0 P1,sa)#zs)" by fastforce
  then have "fst (((Seq P0 P1, sa) # zs)!Suc i) = Q" using zs by fastforce    
  thus ?case using CptnModNestSeq2(8) zs by auto
next 
  case (CptnModNestSeq3 n \<Gamma> P0 sa xsa s'' ys zs P1)  
  then have "P0 = P \<and> P1 = Q \<and> s=Normal sa" by auto  
  moreover then have "(\<Gamma>, (P0, Normal sa) # xsa)\<in> cpn n \<Gamma> P s" 
    using CptnModNestSeq3(1)
    by (simp add: cpn_def)  
  moreover have "last zs=(Throw, Normal s')" using CptnModNestSeq3(10) CptnModNestSeq3.hyps(7) 
    by (simp add: prod_eqI)    
  ultimately show ?case using  CptnModNestSeq3(7)
    using Cons_lift_append by blast      
qed (auto)

lemma Last_Skip_Exist_Final: 
assumes
  a0:"(\<Gamma>,x)\<in>cptn" and
  a1:"x!0 = ((Seq P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"fst(last x) = Skip"  
shows 
  "\<exists>c s' i. i<length x \<and> x!i = (Seq c Q,s') \<and> final (c,s')"
using a0 a1 a2 a3 
proof (induct arbitrary: P s)
  case (CptnOne \<Gamma> c s1) thus ?case by fastforce 
next
  case (CptnEnv \<Gamma> C st t xsa) 
  thus ?case 
  proof -         
    have "LanguageCon.com.Seq P Q = C"
      using CptnEnv.prems(1) by auto
    then show ?thesis
      using CptnEnv.hyps(3) CptnEnv.prems(2) CptnEnv.prems(3) by fastforce
  qed
next
  case (CptnComp \<Gamma> C st C' st' xsa) 
  then have c_seq:"C = (Seq P Q) \<and> st = s" by force
  from CptnComp show ?case proof(cases)
    case (Seqc P1 P1' P2) 
    then have "\<exists>c s' i. i < length ((C', st') # xsa) \<and> 
                        ((C', st') # xsa) ! i = (LanguageCon.com.Seq c Q, s') \<and> 
                        SmallStepCon.final (c, s')"
      using CptnComp last.simps  by fastforce
    thus ?thesis by fastforce 
  next
    case (SeqThrowc C2 s') 
    thus ?thesis 
    proof -
      have "LanguageCon.com.Seq LanguageCon.com.Throw Q = C"
        using \<open>C = LanguageCon.com.Seq LanguageCon.com.Throw C2\<close> c_seq by blast
      then show ?thesis
        using \<open>st = Normal s'\<close> unfolding final_def by force
    qed
  next
    case (FaultPropc) thus ?thesis 
      using c_seq redex_not_Seq by blast
  next
    case (StuckPropc) thus ?thesis 
      using c_seq redex_not_Seq by blast
  next 
    case (AbruptPropc) thus ?thesis
     using c_seq redex_not_Seq by blast 
  qed (auto)
qed

lemma Seq_sound3:                                                       
assumes
  a0:"(n,\<Gamma>,x)\<in>cptn_mod_nest_call" and
  a1:"x!0 = ((Seq P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"fst(last x) = Skip" and
  a4:"env_tran_right \<Gamma> x rely " and
  a5:"snd (x!0)\<in> Normal ` p \<and> Sta p rely \<and> Sta a rely" and
  a6: "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> P sat [p, rely, G, q,a]"
shows
  "False"
using a0 a1 a2 a3 a4 a5 a6
proof (induct arbitrary: P s p) (* p) *)
  case (CptnModNestOne n \<Gamma> C s1)  
    thus ?case by fastforce
next
  case (CptnModNestEnv \<Gamma> C s1 t1 n xsa)
  then have C:"C=Seq P Q" unfolding lift_def by fastforce
  thus ?case
  proof -
     have "((C, t1) # xsa) ! 0 = (LanguageCon.com.Seq P Q, t1)" using C by auto
     moreover have "\<forall>i<length ((C, t1) # xsa). fst (((C, t1) # xsa) ! i) \<noteq> Q"
       using CptnModNestEnv(5) by fastforce
     moreover have "fst (last ((C, t1) # xsa)) = LanguageCon.com.Skip" using CptnModNestEnv(6)
       by (simp add: SmallStepCon.final_def)        
     moreover have "snd (((C, t1) # xsa) ! 0) \<in> Normal ` p" 
       using CptnModNestEnv(8) CptnModNestEnv(1) CptnModNestEnv(7)
       unfolding env_tran_right_def Sta_def by fastforce 
     ultimately show ?thesis
       using CptnModNestEnv(3) CptnModNestEnv(7) CptnModNestEnv(8)  CptnModNestEnv(9) env_tran_tail
       by blast
  qed  
next
  case (CptnModNestSkip)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModNestThrow)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModNestSeq1 n \<Gamma> P0 sa xsa zs P1)
  obtain cl where "fst (last ((LanguageCon.com.Seq P0 P1, sa) # zs)) = Seq cl P1"
    using CptnModNestSeq1(3) by (metis One_nat_def fst_conv last.simps last_conv_nth last_lift map_is_Nil_conv)
  thus ?case using CptnModNestSeq1(6) by auto
next
 case (CptnModNestSeq2 n \<Gamma> P0 sa xsa P1 ys zs) 
  then have "P0 = P \<and> P1 = Q" by auto
  then obtain i where zs:"fst (zs!i) = Q \<and> (i< (length zs))" using CptnModNestSeq2
    by (metis (no_types, lifting) add_diff_cancel_left' fst_conv length_Cons length_append nth_append_length zero_less_Suc zero_less_diff)        
  thus ?case using CptnModNestSeq2(8) zs by auto 
next
   case (CptnModNestSeq3 n \<Gamma> P1 sa xsa s' ys zs Q1 )  
  have s'_a:"s' \<in>  a"   
  proof -
    have  cpnP1:"(\<Gamma>, (P1, Normal sa) # xsa) \<in> cpn n \<Gamma> P1 (Normal sa)" 
      using CptnModNestSeq3.hyps(1)  unfolding  cpn_def
      by fastforce   
    then have  cpP1:"(\<Gamma>, (P1, Normal sa) # xsa) \<in> cp \<Gamma> P1 (Normal sa)" 
      using CptnModNestSeq3.hyps(1)   cptn_mod_nest_cptn_mod cptn_if_cptn_mod unfolding cp_def cpn_def
      by fastforce  
    have map:"((Seq P1 Q1), Normal sa)#(map (lift Q1) xsa) = map (lift Q1)  ((P1, Normal sa) # xsa) "
      using CptnModNestSeq3 by (simp add: Cons_lift) 
    then 
    have "(\<Gamma>,((LanguageCon.com.Seq P1 Q1, Normal sa) # (map (lift Q1) xsa))) \<in> assum (p,rely)"
    proof - 
      have "env_tran_right \<Gamma> ((LanguageCon.com.Seq P1 Q1, Normal sa) # (map (lift Q1) xsa)) rely" 
        using  CptnModNestSeq3(11) CptnModNestSeq3(7) map
        by (metis (no_types) Cons_lift_append CptnModNestSeq3.hyps(7) CptnModNestSeq3.prems(4) env_tran_subr) 
      thus ?thesis using CptnModNestSeq3(12) 
      unfolding assum_def env_tran_right_def by fastforce  
    qed
    moreover have "(\<Gamma>,((Seq P1 Q1), Normal sa)#(map (lift Q1) xsa)) \<in> cpn n \<Gamma> (Seq P1 Q1) (Normal sa)"
      using  CptnModNestSeq3.hyps(1) 
            CptnModNestSeq1
      unfolding  cpn_def by fastforce  
    then have "(\<Gamma>,((Seq P1 Q1), Normal sa)#(map (lift Q1) xsa)) \<in> cp \<Gamma> (Seq P1 Q1) (Normal sa)"
      using CptnModNestSeq3.hyps(1) cp_def cptn_eq_cptn_mod_set 
            cptn_mod.CptnModSeq1 cptn_mod_nest_cptn_mod by fastforce
    ultimately have  "(\<Gamma>, (P1, Normal sa) # xsa) \<in> assum (p,rely)" 
      using assum_map map cpP1 by fastforce
    then have "(\<Gamma>, (P1, Normal sa) # xsa) \<in> comm (G,(q,a)) F" 
      using cpnP1 CptnModNestSeq3(13)  CptnModNestSeq3.prems(1) unfolding com_validityn_def by auto
    thus ?thesis   
      using CptnModNestSeq3(3)  CptnModNestSeq3(4)
      unfolding comm_def final_def by fastforce
  qed
  have "fst (last ((LanguageCon.com.Throw, Normal s') # ys)) = Throw"
  proof -
    have cptn:"(\<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn" 
      using CptnModNestSeq3(5)
      using cptn_eq_cptn_mod_nest by blast 
    moreover have throw_0:"((LanguageCon.com.Throw, Normal s') # ys)!0 = (Throw, Normal s') \<and> 0 < length((LanguageCon.com.Throw, Normal s') # ys)"
      by force         
    moreover have last:"last ((LanguageCon.com.Throw, Normal s') # ys) = ((LanguageCon.com.Throw, Normal s') # ys)!((length ((LanguageCon.com.Throw, Normal s') # ys)) - 1)"
      using last_conv_nth by auto
    moreover have env_tran:"env_tran_right \<Gamma> ((LanguageCon.com.Throw, Normal s') # ys) rely" 
      using  CptnModNestSeq3(11)  CptnModNestSeq3(7) env_tran_subl env_tran_tail by blast           
    ultimately obtain st' where "fst (last ((LanguageCon.com.Throw, Normal s') # ys)) = Throw \<and>        
                     snd (last ((LanguageCon.com.Throw, Normal s') # ys)) = Normal st'" 
    using zero_throw_all_throw[of \<Gamma> "((Throw, Normal s') # ys)" "s'" "(length ((Throw, Normal s') # ys))-1" a rely]
          s'_a CptnModNestSeq3(11) CptnModNestSeq3(12) by fastforce      
    thus ?thesis using CptnModNestSeq3(10) final_def by blast
  qed
  thus ?case using CptnModNestSeq3(10) CptnModNestSeq3(7)
    by force
qed(auto)

lemma map_xs_ys:
  assumes
  a0:"(\<Gamma>, (P0, sa) # xsa) \<in> cptn_mod" and    
  a1:"fst (last ((P0, sa) # xsa)) = C" and
  a2:"(\<Gamma>, (P1, snd (last ((P0, sa) # xsa))) # ys) \<in> cptn_mod" and
  a3:"zs = map (lift P1) xsa @ (P1, snd (last ((P0, sa) # xsa))) # ys" and
  a4:"((LanguageCon.com.Seq P0 P1, sa) # zs) ! 0 = (LanguageCon.com.Seq P Q, s)" and
  a5:"i < length ((LanguageCon.com.Seq P0 P1, sa) # zs) \<and> ((LanguageCon.com.Seq P0 P1, sa) # zs) ! i = (Q, sj)" and
  a6:"\<forall>j<i. fst (((LanguageCon.com.Seq P0 P1, sa) # zs) ! j) \<noteq> Q"
shows 
  "\<exists>xs ys. (\<Gamma>, xs) \<in> cp \<Gamma> P s \<and>
            (\<Gamma>, ys) \<in> cp \<Gamma> Q (snd (xs ! (i - 1))) \<and> (LanguageCon.com.Seq P0 P1, sa) # zs = map (lift Q) xs @ ys"
proof -
  let ?P0 = "(P0, sa) # xsa"
  have P_Q:"P=P0 \<and> s=sa \<and> Q = P1" using a4 by force
  have i:"i=(length ((P0, sa) # xsa))"   
  proof (cases "i=(length ((P0, sa) # xsa))")
    case True thus ?thesis by auto
  next
    case False     
    then have i:"i<(length ((P0, sa) # xsa)) \<or> i > (length ((P0, sa) # xsa))" by auto
    {
      assume i:"i<(length ((P0, sa) # xsa))"
      then have eq_map:"((LanguageCon.com.Seq P0 P1, sa) # zs) ! i = map (lift P1) ((P0, sa) # xsa) ! i" 
        using a3 Cons_lift_append by (metis (no_types, lifting) length_map nth_append) 
      then have  "\<exists>ci si. map (lift P1) ((P0, sa) # xsa) ! i = (Seq ci P1,si)" 
        using i unfolding lift_def
        proof -
          have "map (\<lambda>(c, y). (LanguageCon.com.Seq c P1, y)) ((P0, sa) # xsa) ! i = (case ((P0, sa) # xsa) ! i of (c, x) \<Rightarrow> (LanguageCon.com.Seq c P1, x))"
            by (meson \<open>i < length ((P0, sa) # xsa)\<close> nth_map)
          then show "\<exists>c x. map (\<lambda>(c, x). (LanguageCon.com.Seq c P1, x)) ((P0, sa) # xsa) ! i = (LanguageCon.com.Seq c P1, x)"
            by (simp add: case_prod_beta)
        qed 
      then have  "((LanguageCon.com.Seq P0 P1, sa) # zs) ! i \<noteq> (Q, sj)" 
        using P_Q eq_map by fastforce
      then have ?thesis using a5 by auto
    }note l=this
    {
      assume i:"i>(length ((P0, sa) # xsa))"
      have "fst (((LanguageCon.com.Seq P0 P1, sa) # zs) ! (length ?P0)) = Q"
        using a3 P_Q Cons_lift_append by (metis fstI length_map nth_append_length) 
      then have ?thesis using a6 i by auto
    }
    thus ?thesis using l i by auto
   qed
   then have  "(\<Gamma>, (P0, sa) # xsa) \<in> cp \<Gamma> P s" 
    using a0  cptn_eq_cptn_mod P_Q unfolding cp_def by fastforce
  also have "(\<Gamma>, (P1, snd (last ((P0, sa) # xsa))) # ys) \<in> cp \<Gamma> Q (snd (?P0 ! ((length ?P0) -1)))" 
    using a3 cptn_eq_cptn_mod P_Q unfolding cp_def
  proof -
    have "(\<Gamma>, (Q, snd (last ((P0, sa) # xsa))) # ys) \<in> cptn_mod"
      using a2 P_Q by blast
    then have "(\<Gamma>, (Q, snd (last ((P0, sa) # xsa))) # ys) \<in> {(f, ps). ps ! 0 = (Q, snd (((P0, sa) # xsa) ! (Suc (length xsa) - 1))) \<and> (\<Gamma>, ps) \<in> cptn \<and> f = \<Gamma>}"
      by (simp add: cptn_eq_cptn_mod last_length)
    then show "(\<Gamma>, (P1, snd (last ((P0, sa) # xsa))) # ys) \<in> {(f, ps). ps ! 0 = (Q, snd (((P0, sa) # xsa) ! (length ((P0, sa) # xsa) - 1))) \<and> (\<Gamma>, ps) \<in> cptn \<and> f = \<Gamma>}"
      using P_Q by force
  qed 
  ultimately show ?thesis using a3 P_Q i using Cons_lift_append by blast
qed

lemma map_xs_ys':
  assumes
  a0:"(n, \<Gamma>, (P0, sa) # xsa) \<in> cptn_mod_nest_call" and    
  a1:"fst (last ((P0, sa) # xsa)) = C" and
  a2:"(n,\<Gamma>, (P1, snd (last ((P0, sa) # xsa))) # ys) \<in> cptn_mod_nest_call" and
  a3:"zs = map (lift P1) xsa @ (P1, snd (last ((P0, sa) # xsa))) # ys" and
  a4:"((LanguageCon.com.Seq P0 P1, sa) # zs) ! 0 = (LanguageCon.com.Seq P Q, s)" and
  a5:"i < length ((LanguageCon.com.Seq P0 P1, sa) # zs) \<and> ((LanguageCon.com.Seq P0 P1, sa) # zs) ! i = (Q, sj)" and
  a6:"\<forall>j<i. fst (((LanguageCon.com.Seq P0 P1, sa) # zs) ! j) \<noteq> Q"
shows 
  "\<exists>xs ys. (\<Gamma>, xs) \<in> cpn n \<Gamma> P s \<and>
            (\<Gamma>, ys) \<in> cpn n \<Gamma> Q (snd (xs ! (i - 1))) \<and> (LanguageCon.com.Seq P0 P1, sa) # zs = map (lift Q) xs @ ys"
proof -
  let ?P0 = "(P0, sa) # xsa"
  have P_Q:"P=P0 \<and> s=sa \<and> Q = P1" using a4 by force
  have i:"i=(length ((P0, sa) # xsa))"   
  proof (cases "i=(length ((P0, sa) # xsa))")
    case True thus ?thesis by auto
  next
    case False     
    then have i:"i<(length ((P0, sa) # xsa)) \<or> i > (length ((P0, sa) # xsa))" by auto
    {
      assume i:"i<(length ((P0, sa) # xsa))"
      then have eq_map:"((LanguageCon.com.Seq P0 P1, sa) # zs) ! i = map (lift P1) ((P0, sa) # xsa) ! i" 
        using a3 Cons_lift_append by (metis (no_types, lifting) length_map nth_append) 
      then have  "\<exists>ci si. map (lift P1) ((P0, sa) # xsa) ! i = (Seq ci P1,si)" 
        using i unfolding lift_def
        proof -
          have "map (\<lambda>(c, y). (LanguageCon.com.Seq c P1, y)) ((P0, sa) # xsa) ! i = (case ((P0, sa) # xsa) ! i of (c, x) \<Rightarrow> (LanguageCon.com.Seq c P1, x))"
            by (meson \<open>i < length ((P0, sa) # xsa)\<close> nth_map)
          then show "\<exists>c x. map (\<lambda>(c, x). (LanguageCon.com.Seq c P1, x)) ((P0, sa) # xsa) ! i = (LanguageCon.com.Seq c P1, x)"
            by (simp add: case_prod_beta)
        qed 
      then have  "((LanguageCon.com.Seq P0 P1, sa) # zs) ! i \<noteq> (Q, sj)" 
        using P_Q eq_map by fastforce
      then have ?thesis using a5 by auto
    }note l=this
    {
      assume i:"i>(length ((P0, sa) # xsa))"
      have "fst (((LanguageCon.com.Seq P0 P1, sa) # zs) ! (length ?P0)) = Q"
        using a3 P_Q Cons_lift_append by (metis fstI length_map nth_append_length) 
      then have ?thesis using a6 i by auto
    }
    thus ?thesis using l i by auto
   qed
   then have  "(\<Gamma>, (P0, sa) # xsa) \<in> cpn n \<Gamma> P s" 
    using a0  P_Q unfolding cpn_def by fastforce
  also have "(\<Gamma>, (P1, snd (last ((P0, sa) # xsa))) # ys) \<in> cpn n \<Gamma> Q (snd (?P0 ! ((length ?P0) -1)))" 
    using a3 cptn_eq_cptn_mod P_Q unfolding cpn_def
  proof -
    have "(n, \<Gamma>, (Q, snd (last ((P0, sa) # xsa))) # ys) \<in> cptn_mod_nest_call"
      using a2 P_Q by blast
    then have "(\<Gamma>, (Q, snd (last ((P0, sa) # xsa))) # ys) \<in> {(f, ps). ps ! 0 = (Q, snd (((P0, sa) # xsa) ! (Suc (length xsa) - 1))) \<and> 
              (n, \<Gamma>, ps) \<in> cptn_mod_nest_call \<and> f = \<Gamma>}"
      by (simp add: cptn_eq_cptn_mod last_length)
    then show "(\<Gamma>, (P1, snd (last ((P0, sa) # xsa))) # ys) \<in> {(f, ps). ps ! 0 = (Q, snd (((P0, sa) # xsa) ! (length ((P0, sa) # xsa) - 1))) \<and> (n,\<Gamma>, ps) \<in> cptn_mod_nest_call \<and> f = \<Gamma>}"
      using P_Q by force
  qed 
  ultimately show ?thesis using a3 P_Q i using Cons_lift_append by blast
qed



lemma Seq_sound4: 
assumes
  a0:"(n,\<Gamma>,x)\<in>cptn_mod_nest_call" and
  a1:"x!0 = ((Seq P Q),s)" and
  a2:"i<length x \<and> x!i=(Q,sj)" and
  a3:"\<forall>j<i. fst(x!j)\<noteq>Q" and 
  a4:"env_tran_right \<Gamma> x rely" and
  a5:"snd (x!0)\<in> Normal ` p \<and> Sta p rely \<and> Sta a rely" and
  a6: "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> P sat [p, rely, G, q,a]"
shows
  "\<exists>xs ys. (\<Gamma>,xs) \<in> (cpn n \<Gamma> P s) \<and> (\<Gamma>,ys) \<in> (cpn n \<Gamma> Q (snd (xs!(i-1)))) \<and> x = (map (lift Q) xs)@ys"
using a0 a1 a2 a3 a4 a5 a6
proof (induct arbitrary: i sj P s p) 
   case (CptnModNestOne \<Gamma> C s1)  
    thus ?case by fastforce
next
  case (CptnModNestEnv \<Gamma> C st t n xsa)    
  have a1:"Seq P Q \<noteq> Q" by simp    
  then have C_seq:"C=(Seq P Q)" using CptnModNestEnv by fastforce
  then have "fst(((C, st) # (C, t) # xsa)!0) \<noteq>Q" using CptnEnv a1 by auto
  moreover have  n_q:"fst(((C, st) # (C, t) # xsa)!1) \<noteq>Q" using CptnModNestEnv a1 by auto
  moreover have "fst(((C, st) # (C, t) # xsa)!i) =Q" using CptnModNestEnv by auto
  ultimately have i_suc: "i> (Suc 0)" 
    by (metis Suc_eq_plus1 Suc_lessI add.left_neutral neq0_conv) 
  then obtain i' where i':"i=Suc i'" by (meson lessE) 
  then have i_minus:"i'=i-1" by auto
  have c_init:"((C, t) # xsa) ! 0 = ((Seq P Q), t)"
    using CptnModNestEnv by auto 
  moreover have "i'< length ((C,t)#xsa) \<and> ((C,t)#xsa)!i' = (Q,sj)"
    using i' CptnModNestEnv(5) by force
  moreover have "\<forall>j<i'. fst (((C, t) # xsa) ! j) \<noteq> Q"
    using i' CptnModNestEnv(6) by force
  moreover have "snd (((C, t) # xsa) ! 0) \<in> Normal ` p" 
       using CptnModNestEnv(8) CptnModNestEnv(1) CptnModNestEnv(7)
       unfolding env_tran_right_def Sta_def by fastforce 
  ultimately have hyp:"\<exists>xs ys.
     (\<Gamma>, xs) \<in> cpn n \<Gamma> P t \<and>
     (\<Gamma>, ys) \<in> cpn n \<Gamma> Q (snd (xs ! (i'-1))) \<and> (C, t) # xsa = map (lift Q) xs @ ys"
    using CptnModNestEnv(3) env_tran_tail  CptnModNestEnv(8) CptnModNestEnv(9) 
         CptnModNestEnv.prems(4) by blast  
  then obtain xs ys where xs_cp:"(\<Gamma>, xs) \<in> cpn n \<Gamma> P t \<and>
     (\<Gamma>, ys) \<in> cpn n \<Gamma> Q (snd (xs ! (i'-1))) \<and> (C, t) # xsa = map (lift Q) xs @ ys"
    by fast
  have "(\<Gamma>, (P,s)#xs) \<in> cpn n \<Gamma> P s"
  proof -
    have "xs!0 = (P,t)" 
      using xs_cp unfolding cpn_def by blast
    moreover have "xs\<noteq>[]"
      using xs_cp  n_q c_init unfolding cpn_def by auto 
    ultimately obtain xs' where xs':"(n, \<Gamma>, (P,t)#xs') \<in> cptn_mod_nest_call \<and> xs=(P,t)#xs'" 
      using SmallStepCon.nth_tl xs_cp unfolding cpn_def by force
    thus ?thesis 
    proof -
      have "(LanguageCon.com.Seq P Q, s) = (C, st)"
        using CptnModNestEnv.prems(1) by auto
      then have "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow>\<^sub>e (P, t)"
        using Seq_env_P CptnModNestEnv(1) by blast
      then show ?thesis
        by (simp add:xs' cpn_def cptn_mod_nest_call.CptnModNestEnv)
    qed
  qed
  thus  ?case 
    using i_suc Cons_lift_append CptnModNestEnv.prems(1) i' i_minus xs_cp
    by fastforce   
next
  case (CptnModNestSkip)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModNestThrow)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModNestSeq1 n \<Gamma> P0 sa xsa zs P1)  
  then have P1_Q:"P1 = Q" by auto
  let ?x = "(LanguageCon.com.Seq P0 P1, sa) # zs"
  have "\<forall>j<length ?x. \<exists>c s. ?x!j = (Seq c P1,s)" using CptnModNestSeq1(3)
  proof (induct xsa arbitrary: zs P0 P1 sa)
    case Nil thus ?case by auto
  next
    case (Cons a xsa) 
    then obtain ac as where "a=(ac,as)" by fastforce
    then have zs:"zs = (Seq ac P1,as)#(map (lift P1)  xsa)" 
      using Cons(2) 
      unfolding lift_def  by auto
    have zs_eq:"(map (lift P1)  xsa)=(map (lift P1)  xsa)" by auto
    note hyp=Cons(1)[OF zs_eq] 
    note hyp[of ac as]
    thus ?case using zs Cons(2) by (metis One_nat_def diff_Suc_Suc diff_zero length_Cons less_Suc_eq_0_disj nth_Cons') 
  qed  
  thus ?case using P1_Q CptnModNestSeq1(5) using fstI seq_not_eq2 by auto
next
  case (CptnModNestSeq2 n \<Gamma> P0 sa xsa P1 ys zs) 
  then show ?case using map_xs_ys'[OF CptnModNestSeq2(1) CptnModNestSeq2(3) CptnModNestSeq2(4) CptnModNestSeq2(6)
                              CptnModNestSeq2(7) CptnModNestSeq2(8) CptnModNestSeq2(9)] by blast
next 
  case (CptnModNestSeq3 n \<Gamma> P1 sa xsa s' ys zs Q1 ) 
  then have P_Q:"P=P1 \<and> Q = Q1" by force
  thus ?case
  proof (cases "Q1 = Throw")
    case True thus ?thesis using map_xs_ys'[of n \<Gamma> P1 "Normal sa" xsa Throw Throw ys zs] 
      CptnModNestSeq3 by fastforce
  next 
    case False note q_not_throw=this
    have "\<forall>x. x< length ((LanguageCon.com.Seq P1 Q1, Normal sa) # zs) \<longrightarrow>
              ((LanguageCon.com.Seq P1 Q1, Normal sa) # zs) ! x \<noteq> (Q, sj)"
    proof -
    {
      fix x
      assume x_less:"x< length ((LanguageCon.com.Seq P1 Q1, Normal sa) # zs)"
      have "((LanguageCon.com.Seq P1 Q1, Normal sa) # zs) ! x \<noteq> (Q, sj)"
      proof (cases "x < length ((LanguageCon.com.Seq P1 Q1, Normal sa)#map (lift Q1) xsa)")
        case True 
        then have eq_map:"((LanguageCon.com.Seq P1 Q1, Normal sa) # zs) ! x = map (lift Q1) ((P1, Normal sa) # xsa) ! x"           
          by (metis (no_types) Cons_lift Cons_lift_append CptnModNestSeq3.hyps(7) True nth_append)
        then have  "\<exists>ci si. map (lift Q1) ((P1, Normal sa) # xsa) ! x = (Seq ci Q1,si)" 
          using True unfolding lift_def
        proof -
          have "x < length ((P1, Normal sa) # xsa)"
            using True by auto
          then have "map (\<lambda>(c, y). (LanguageCon.com.Seq c Q1, y)) ((P1, Normal sa) # xsa) ! x = (case ((P1, Normal sa) # xsa) ! x of (c, x) \<Rightarrow> (LanguageCon.com.Seq c Q1, x))"
            using nth_map by blast
          then show "\<exists>c x1. map (\<lambda>(c, x1). (LanguageCon.com.Seq c Q1, x1)) ((P1, Normal sa) # xsa) ! x = (LanguageCon.com.Seq c Q1, x1)"
            by (simp add: case_prod_beta')
        qed            
        then have  "((LanguageCon.com.Seq P1 Q1, Normal sa) # zs) ! x \<noteq> (Q, sj)" 
          using P_Q eq_map by fastforce     
        thus ?thesis using CptnModNestSeq3(10) by auto        
      next
        case False 
        have s'_a:"s' \<in>  a"   
        proof -
        have  cpP1:"(\<Gamma>, (P1, Normal sa) # xsa) \<in> cpn n \<Gamma> P1 (Normal sa)" 
          using CptnModNestSeq3.hyps(1) cptn_eq_cptn_mod_set unfolding cpn_def by fastforce
        then have  cpP1':"(\<Gamma>, (P1, Normal sa) # xsa) \<in> cp \<Gamma> P1 (Normal sa)" 
          unfolding cpn_def cp_def
          using cptn_if_cptn_mod cptn_mod_nest_cptn_mod by fastforce 
        have map:"((Seq P1 Q1), Normal sa)#(map (lift Q1) xsa) = map (lift Q1)  ((P1, Normal sa) # xsa) "
          using CptnModSeq3 by (simp add: Cons_lift) 
        then 
        have "(\<Gamma>,((LanguageCon.com.Seq P1 Q1, Normal sa) # (map (lift Q1) xsa))) \<in> assum (p,rely)"
        proof - 
          have "env_tran_right \<Gamma> ((LanguageCon.com.Seq P1 Q1, Normal sa) # (map (lift Q1) xsa)) rely" 
            using  CptnModNestSeq3(11) CptnModNestSeq3(7) map
            by (metis (no_types) Cons_lift_append CptnModNestSeq3.hyps(7) CptnModNestSeq3.prems(4) env_tran_subr) 
          thus ?thesis using CptnModNestSeq3(12) 
          unfolding assum_def env_tran_right_def by fastforce  
        qed
        moreover have "(\<Gamma>,((Seq P1 Q1), Normal sa)#(map (lift Q1) xsa)) \<in> cpn n \<Gamma> (Seq P1 Q1) (Normal sa)"
          using CptnModNestSeq3(7) CptnModNestSeq3.hyps(1) cptn_eq_cptn_mod_set cptn_mod_nest_call.CptnModNestSeq1 
          unfolding cpn_def  by fastforce  
        then have  "(\<Gamma>,((Seq P1 Q1), Normal sa)#(map (lift Q1) xsa)) \<in> cp \<Gamma> (Seq P1 Q1) (Normal sa)"
          unfolding cpn_def cp_def
          by (simp add: cptn_if_cptn_mod cptn_mod_nest_cptn_mod)
        ultimately have  "(\<Gamma>, (P1, Normal sa) # xsa) \<in> assum (p,rely)" 
          using assum_map map cpP1' by fastforce
        then have "(\<Gamma>, (P1, Normal sa) # xsa) \<in> comm (G,(q,a)) F" 
          using cpP1 CptnModNestSeq3(13)  CptnModNestSeq3.prems(1) unfolding com_validityn_def by auto
        thus ?thesis   
          using CptnModNestSeq3(3)  CptnModNestSeq3(4)
          unfolding comm_def final_def by fastforce
      qed
      have all_throw:"\<forall>i<length ((LanguageCon.com.Throw, Normal s')# ys). 
              fst (((LanguageCon.com.Throw, Normal s')# ys)!i) = Throw"
      proof -
       {fix i
        assume i:"i< length ((LanguageCon.com.Throw, Normal s')# ys)"
        have cptn:"(n, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call" 
          using CptnModNestSeq3(5) by auto
        moreover have throw_0:"((LanguageCon.com.Throw, Normal s') # ys)!0 = (Throw, Normal s') \<and> 0 < length((LanguageCon.com.Throw, Normal s') # ys)"
          by force         
        moreover have last:"last ((LanguageCon.com.Throw, Normal s') # ys) = ((LanguageCon.com.Throw, Normal s') # ys)!((length ((LanguageCon.com.Throw, Normal s') # ys)) - 1)"
          using last_conv_nth by auto
        moreover have env_tran:"env_tran_right \<Gamma> ((LanguageCon.com.Throw, Normal s') # ys) rely" 
          using  CptnModNestSeq3(11)  CptnModNestSeq3(7) env_tran_subl env_tran_tail by blast           
        ultimately have 
             "fst (((LanguageCon.com.Throw, Normal s')# ys)!i) = Throw"          
        using zero_throw_all_throw[of \<Gamma> "((Throw, Normal s') # ys)" "s'" "i" a rely]
              s'_a  CptnModNestSeq3(12) i
        using cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod by auto
        }     
        thus ?thesis using CptnModNestSeq3(10) final_def by blast        
      qed      
      then have 
        "\<forall>x\<ge> length ((LanguageCon.com.Seq P1 Q1, Normal sa) # map (lift Q1) xsa). 
           x<length (((LanguageCon.com.Seq P1 Q1, Normal sa) # zs)) \<longrightarrow>
              fst (((LanguageCon.com.Seq P1 Q1, Normal sa) # zs) ! x) = Throw"  
      proof-
      {
        fix x 
        assume a1:"x\<ge> length ((LanguageCon.com.Seq P1 Q1, Normal sa) # map (lift Q1) xsa)" and
               a2:"x<length (((LanguageCon.com.Seq P1 Q1, Normal sa) # zs))"
        then have "((LanguageCon.com.Seq P1 Q1, Normal sa) # zs) ! x = 
                   ((LanguageCon.com.Throw, Normal s')# ys) !(x - (length ((LanguageCon.com.Seq P1 Q1, Normal sa) # map (lift Q1) xsa)))"
        using CptnModNestSeq3(7) by (metis Cons_lift Cons_lift_append not_le nth_append)
        then have"fst (((LanguageCon.com.Seq P1 Q1, Normal sa) # zs) ! x) = Throw" 
          using all_throw a1 a2 CptnModNestSeq3.hyps(7)  by auto 
      } thus ?thesis by auto
      qed       
      thus ?thesis using False CptnModNestSeq3(7) q_not_throw P_Q x_less 
        by (metis fst_conv not_le)  
    qed
    } thus ?thesis by auto
    qed
    thus ?thesis using CptnModNestSeq3(9) by fastforce    
  qed
qed(auto)



inductive_cases stepc_elim_cases_Seq_throw:
"\<Gamma>\<turnstile>\<^sub>c(Seq c1 c2,s) \<rightarrow> (Throw, Normal s1)" 

inductive_cases stepc_elim_cases_Seq_skip_c2:
"\<Gamma>\<turnstile>\<^sub>c(Seq c1 c2,s) \<rightarrow> (c2,s)"


lemma seq_skip_throw:
 "\<Gamma>\<turnstile>\<^sub>c(Seq c1 c2,s) \<rightarrow> (c2,s)  \<Longrightarrow> c1= Skip \<or> (c1=Throw \<and> (\<exists>s2'. s=Normal s2'))"
apply (rule stepc_elim_cases_Seq_skip_c2)
apply fastforce
apply (auto)+
apply (fastforce intro:redex_not_Seq)+
done

lemma Seq_sound: 
      "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p, R, G, q,a] \<Longrightarrow>
       \<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p, R, G, q,a] \<Longrightarrow>
       \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [q, R, G, r,a] \<Longrightarrow>
       \<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c2 sat [q, R, G, r,a] \<Longrightarrow>        
       Sta a R \<and> Sta p R \<Longrightarrow>  (\<forall>s. (Normal s,Normal s) \<in> G) \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (Seq c1 c2) sat [p, R, G, r,a]"
proof -  
  assume
    a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p, R, G, q,a]" and
    a1:"\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p, R, G, q,a]" and
    a2:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [q, R, G, r,a]" and    
    a3: "\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c2 sat [q, R, G, r,a]" and     
    a4: "Sta a R \<and> Sta p R" and
    a5: "(\<forall>s. (Normal s, Normal s) \<in> G)"
  { 
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"
    then have a1:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p, R, G, q,a]" 
      using a1 com_cvalidityn_def by fastforce  
    then have a3: "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c2 sat [q, R, G, r,a]"
      using a3 com_cvalidityn_def all_call by fastforce 
    have "cpn n \<Gamma> (Seq c1 c2)  s \<inter> assum(p, R) \<subseteq> comm(G, (r,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cpn n \<Gamma> (Seq c1 c2) s" and a11:"c \<in> assum(p, R)"
      then have a10':"c \<in> cp \<Gamma> (Seq c1 c2) s" unfolding cpn_def cp_def
        using cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod by fastforce
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have cp:"l!0=((Seq c1 c2),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10' cp_def c_prod by fastforce
      have cptn_nest:"l!0=((Seq c1 c2),s) \<and> (n,\<Gamma>,l) \<in> cptn_mod_nest_call \<and> \<Gamma>=\<Gamma>1" using a10 cpn_def c_prod by fastforce
      have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast
      have "c \<in> comm(G, (r,a)) F"         
      proof - 
      {
       assume l_f:"snd (last l) \<notin> Fault ` F"       
       have assum:"snd(l!0) \<in> Normal ` (p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                 (snd(l!i), snd(l!(Suc i))) \<in> R)" 
       using a11 c_prod unfolding assum_def by simp
       then have env_tran:"env_tran \<Gamma> p l R" using env_tran_def cp by blast
       then have env_tran_right: "env_tran_right \<Gamma> l R" 
         using env_tran env_tran_right_def unfolding env_tran_def by auto       
       have "(\<forall>i. Suc i<length l \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow>                                             
                 (snd(l!i), snd(l!(Suc i))) \<in> G)\<and>
             (final (last l)  \<longrightarrow>                    
                   ((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal `  r)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` a))"
       proof (cases "\<forall>i<length l. fst (l!i)\<noteq> c2")
         case True 
         then have no_c2:"\<forall>i<length l. fst (l!i)\<noteq> c2" by assumption
         show ?thesis
         proof (cases "final (last l)")
           case True
           then obtain s' where "fst (last l) = Skip \<or> (fst (last l) = Throw \<and> snd (last l) = Normal s')"  
             using final_def by fast           
           thus ?thesis
           proof
             assume "fst (last l) = LanguageCon.com.Skip" 
             then have "False" 
               using  no_c2 env_tran_right cptn_nest cptn_eq_cptn_mod_set Seq_sound3 a4 a1 assum
               by blast
             thus ?thesis by auto
           next             
             assume asm0:"fst (last l) = LanguageCon.com.Throw \<and> snd (last l) = Normal s'"
             then obtain lc1 s1' ys where cpn_lc1:"(\<Gamma>,lc1) \<in> cpn n \<Gamma> c1 s \<and> l = ((map (lift c2) lc1)@((Throw, Normal s1')#ys))"
               using Seq_sound2'[of n \<Gamma> l c1 c2 s s']  cptn_nest cptn_eq_cptn_mod_set env_tran_right no_c2 by blast
             then have cp_lc1:"(\<Gamma>,lc1) \<in> cp \<Gamma> c1 s"
               using  cptn_if_cptn_mod cptn_mod_nest_cptn_mod split_conv 
               unfolding cp_def cpn_def by blast
             let ?m_lc1 = "map (lift c2) lc1"
             let ?lm_lc1 = "(length ?m_lc1)"
             let ?last_m_lc1 = "?m_lc1!(?lm_lc1-1)"             
             have lc1_not_empty:"lc1 \<noteq> []"
               using \<Gamma>1 a10  cpn_lc1 cp by auto 
             then have map_cpn:"(\<Gamma>,?m_lc1) \<in> cpn n \<Gamma> (Seq c1 c2) s"                  
             proof -
               have f1: "lc1 ! 0 = (c1, s) \<and> (n,\<Gamma>, lc1) \<in> cptn_mod_nest_call \<and> \<Gamma> = \<Gamma>"
                 using cpn_lc1 cpn_def by blast
               then have f2: "(n, \<Gamma>, ?m_lc1) \<in> cptn_mod_nest_call" 
               by (metis (no_types) Cons_lift cptn_mod_nest_call.CptnModNestSeq1 f1 lc1_not_empty list.exhaust nth_Cons_0)                               
               then show ?thesis
                 using f2 f1 lc1_not_empty by (simp add: cpn_def lift_def)
             qed
             then have map_cp:"(\<Gamma>,?m_lc1) \<in> cp \<Gamma> (Seq c1 c2) s"
               by (metis (no_types, lifting) cp_def cp_lc1 cpn_def lift_is_cptn mem_Collect_eq split_conv) 
             also have map_assum:"(\<Gamma>,?m_lc1) \<in> assum (p,R)"
               using sub_assum a10 a11 \<Gamma>1 cpn_lc1 lc1_not_empty 
               by (metis SmallStepCon.nth_tl map_is_Nil_conv)
             ultimately have "((\<Gamma>,lc1) \<in> assum(p, R))"  
               using \<Gamma>1 assum_map cp_lc1 by blast                          
             then have lc1_comm:"(\<Gamma>,lc1) \<in> comm(G, (q,a)) F"  
               using a1  cpn_lc1 unfolding com_validityn_def by blast
             then have m_lc1_comm:"(\<Gamma>,?m_lc1) \<in> comm(G, (q,a)) F"
               using map_cp map_assum comm_map cp_lc1 by fastforce
             then have last_m_lc1:"last (?m_lc1) = (Seq (fst (last lc1)) c2,snd (last lc1))"
             proof -
               have a000:"\<forall>p c. (LanguageCon.com.Seq (fst p) c, snd p) = lift c p"
                 using Cons_lift by force
               then show ?thesis
                 by (simp add: last_map a000 lc1_not_empty)
             qed
             then have last_length:"last (?m_lc1) = ?last_m_lc1"  
               using lc1_not_empty last_conv_nth list.map_disc_iff by blast 
             then have l_map:"l!(?lm_lc1-1)= ?last_m_lc1" 
               using cpn_lc1
               by (simp add:lc1_not_empty nth_append)
             then have lm_lc1:"l!(?lm_lc1) = (Throw, Normal s1')"
               using cpn_lc1 by (meson nth_append_length) 
             then have step:"\<Gamma>\<turnstile>\<^sub>c(l!(?lm_lc1-1)) \<rightarrow> (l!(?lm_lc1))"
             proof -
               have "\<Gamma>\<turnstile>\<^sub>c(l!(?lm_lc1-1)) \<rightarrow>\<^sub>c\<^sub>e (l!(?lm_lc1))"
               proof -
                 have f1: "\<forall>n na. \<not> n < na \<or> Suc (na - Suc n) = na - n"
                   by (meson Suc_diff_Suc)
                 have "map (lift c2) lc1 \<noteq> []"
                   by (metis lc1_not_empty map_is_Nil_conv)
                 then have f2: "0 < length (map (lift c2) lc1)"
                   by (meson length_greater_0_conv)
                 then have "length (map (lift c2) lc1) - 1 + 1 < length (map (lift c2) lc1 @ (LanguageCon.com.Throw, Normal s1') # ys)"
                   by simp
                 then show ?thesis
                   using f2 f1
                   by (metis Suc_pred' cp cpn_lc1 cptn_tran_ce_i)
               qed
               moreover have "\<not>\<Gamma>\<turnstile>\<^sub>c(l!(?lm_lc1-1)) \<rightarrow>\<^sub>e (l!(?lm_lc1))"
               using  last_m_lc1 last_length l_map
               proof -
                 have "(LanguageCon.com.Seq (fst (last lc1)) c2, snd (last lc1)) = l ! (length (map (lift c2) lc1) - 1)"
                   using l_map last_m_lc1 local.last_length by presburger
                 then show ?thesis
                   by (metis (no_types) LanguageCon.com.distinct(71) \<open>l ! length (map (lift c2) lc1) = (LanguageCon.com.Throw, Normal s1')\<close> env_c_c')
               qed
               ultimately show ?thesis using step_ce_elim_cases by blast        
             qed
             then have last_lc1_suc:"snd (l!(?lm_lc1-1)) = snd (l!?lm_lc1) \<and> fst (l!(?lm_lc1-1)) = Seq Throw c2"
               using lm_lc1 stepc_elim_cases_Seq_throw
               by (metis One_nat_def asm0 append_is_Nil_conv cpn_lc1 diff_Suc_less fst_conv l_map last_conv_nth last_m_lc1 length_greater_0_conv list.simps(3) local.last_length no_c2 snd_conv)                            
             then have a_normal:"snd (l!?lm_lc1) \<in> Normal ` (a)" 
             proof
               have last_lc1:"fst (last lc1) = Throw \<and> snd (last lc1) = Normal s1'" 
               using last_length l_map lm_lc1 last_m_lc1 last_lc1_suc
               by (metis LanguageCon.com.inject(3) fst_conv snd_conv)  
               have "final (last lc1)" using last_lc1 final_def 
                 by blast
               moreover have "snd (last lc1)\<notin> Fault ` F" 
                 using last_lc1 by fastforce
               ultimately have "(fst (last lc1) = Throw \<and> 
                      snd (last lc1) \<in> Normal ` (a))" 
                 using lc1_comm last_lc1 unfolding comm_def by force
               thus ?thesis  using  l_map last_lc1_suc last_m_lc1 last_length by auto
             qed                                         
             have concl:"(\<forall>i. Suc i<length l \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow>                                           
                 (snd(l!i), snd(l!(Suc i))) \<in> G)"
             proof-
             { fix k ns ns'
               assume a00:"Suc k<length l" and
                a21:"\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))"   
                then have i_m_l:"\<forall>i <?lm_lc1  . l!i = ?m_lc1!i" 
                  using cp_lc1
                proof -
                  have "map (lift c2) lc1 \<noteq> []"
                    by (meson lc1_not_empty list.map_disc_iff)
                  then show ?thesis
                    by (metis (no_types) cpn_lc1  nth_append)
                qed
                have last_not_F:"snd (last ?m_lc1) \<notin> Fault ` F" 
                   using l_map last_lc1_suc lm_lc1 last_length by auto 
                have "(snd(l!k), snd(l!(Suc k))) \<in> G"
                proof (cases "Suc k< ?lm_lc1")
                  case True 
                  then have a11': "\<Gamma>\<turnstile>\<^sub>c(?m_lc1!k)  \<rightarrow> (?m_lc1!(Suc k))" 
                    using a11 i_m_l True
                  proof -
                    have "\<forall>n na. \<not> 0 < n - Suc na \<or> na < n "
                      using diff_Suc_eq_diff_pred zero_less_diff by presburger
                    then show ?thesis
                      by (metis (no_types)  True a21 i_m_l  zero_less_diff)
                  qed                  
                  then have "(snd(?m_lc1!k), snd(?m_lc1!(Suc k))) \<in> G"
                  using a11' m_lc1_comm True comm_dest1 l_f last_not_F by fastforce
                  thus ?thesis using i_m_l using  True by fastforce
                next
                  case False 
                  then have "(Suc k=?lm_lc1) \<or> (Suc k>?lm_lc1)" by auto
                  thus ?thesis 
                  proof
                    {assume suck:"(Suc k=?lm_lc1)"
                     then have k:"k=?lm_lc1-1" by auto
                     have G_s1':"(Normal s1', Normal s1')\<in>G" 
                       using a5 by auto               
                     then show "(snd (l!k), snd (l!Suc k)) \<in> G"               
                     proof -
                       have "snd (l!Suc k) = Normal s1'" 
                         using lm_lc1 suck by fastforce                                
                       then show ?thesis using suck k G_s1' last_lc1_suc by fastforce
                     qed
                    }
                  next
                  { 
                    assume a001:"Suc k>?lm_lc1"
                    have "\<forall>i. i\<ge>(length lc1) \<and> (Suc i < length l) \<longrightarrow> 
                            \<not>(\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))"
                    using lm_lc1 lc1_not_empty
                    proof -
                      have "env_tran_right \<Gamma> l R"
                        by (metis  env_tran_right)
                      then show ?thesis 
                       using a_normal cp fst_conv length_map 
                             lm_lc1 only_one_component_tran_j[of \<Gamma> l ?lm_lc1 s1' a k R] snd_conv a21 a001 a00
                             a4 by auto
                    qed
                    then have "\<not>(\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
                      using a00 a001  by auto                    
                    then show ?thesis using a21 by fastforce                    
                  }
                  qed 
                qed
              } thus ?thesis by auto 
             qed 
             have concr:"(final (last l)  \<longrightarrow>                    
                   ((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` r)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` a))" 
             proof -
               have l_t:"fst (last l) = Throw" 
                 using lm_lc1 by (simp add: asm0)
               have "?lm_lc1 \<le> length l -1" using cpn_lc1 by fastforce
               then have "snd (l ! (length l - 1)) \<in> Normal ` a"
                 using  cp a_normal a4  fst_conv  lm_lc1 snd_conv 
                         env_tran_right i_throw_all_throw[of \<Gamma> l ?lm_lc1 s1' "(length l -1)" _ R a ]
                       by (metis (no_types, lifting) One_nat_def diff_is_0_eq diff_less diff_less_Suc diff_zero image_iff length_greater_0_conv lessI less_antisym list.size(3) xstate.inject(1))                               
               thus ?thesis using l_t 
                 by (simp add:  cpn_lc1 last_conv_nth)
             qed
             note res = conjI [OF concl concr]
             then show ?thesis using  \<Gamma>1 c_prod unfolding comm_def by auto
           qed                  
         next
           case False
           then obtain lc1 where cpn_lc1:"(\<Gamma>,lc1) \<in> cpn n \<Gamma> c1 s \<and> l = map (lift c2) lc1" 
             using Seq_sound1 assum False no_c2 env_tran_right cptn_nest cptn_eq_cptn_mod_set a4 a1 
             by blast          
           then have cp_lc1:"(\<Gamma>,lc1) \<in> cp \<Gamma> c1 s "
             using cp_def cpn_def cptn_if_cptn_mod cptn_mod_nest_cptn_mod by fastforce              
           then have "((\<Gamma>,lc1) \<in> assum(p, R))"  
              using \<Gamma>1  cpn_lc1 a10' a11 assum_map by blast
           then have "(\<Gamma>, lc1)\<in> comm(G, (q,a)) F" using cpn_lc1 a1
             by (meson IntI com_validityn_def contra_subsetD)
           then have "(\<Gamma>, l)\<in> comm(G, (r,a)) F"
             using comm_map a10' \<Gamma>1 cp_lc1 cpn_lc1 by blast
           then show ?thesis using l_f
             unfolding comm_def by auto
         qed
       next         
         case False 
         then obtain k where k_len:"k<length l \<and> fst (l ! k) = c2"
           by blast         
         then have "\<exists>m. (m < length l \<and> fst (l ! m) = c2) \<and>
                   (\<forall>i<m. \<not> (i < length l \<and> fst (l ! i) = c2))"   
           using a0 exists_first_occ[of "(\<lambda>i. i<length l  \<and> fst (l ! i) = c2)" k] 
           by blast
         then obtain i where a0:"i<length l \<and> fst (l !i) = c2 \<and>
                                (\<forall>j<i. (fst (l ! j) \<noteq> c2))"
           by fastforce        
         then obtain s2 where li:"l!i =(c2,s2)" by (meson eq_fst_iff)
         then obtain lc1 lc2 where cp_lc1:"(\<Gamma>,lc1) \<in> (cpn n \<Gamma> c1 s) \<and> 
                                 (\<Gamma>,lc2) \<in> (cpn n \<Gamma> c2 (snd (lc1!(i-1)))) \<and> 
                                 l = (map (lift c2) lc1)@lc2"
           using Seq_sound4[of n \<Gamma> l c1 c2 s] a0 env_tran_right a4 a1 cptn_nest assum by blast  
         then have cp_lc1':"(\<Gamma>,lc1) \<in> (cp  \<Gamma> c1 s) \<and> 
                    (\<Gamma>,lc2) \<in> (cp  \<Gamma> c2 (snd (lc1!(i-1))))"
           unfolding cp_def cpn_def cptn_eq_cptn_mod_nest by fastforce
         have "\<forall>i < length l. snd (l!i) \<notin> Fault ` F"
           using cp l_f last_not_F[of \<Gamma> l F] by blast  
         then have i_not_fault:"snd (l!i) \<notin> Fault ` F" using a0 by blast
         have length_c1_map:"length lc1 = length (map (lift c2) lc1)" 
           by fastforce      
         then have i_map:"i=length lc1" 
           using cp_lc1 li a0 unfolding lift_def
         proof -
            assume a1: "(\<Gamma>, lc1) \<in> cpn n \<Gamma> c1 s \<and> (\<Gamma>, lc2) \<in> cpn n \<Gamma> c2 (snd (lc1 ! (i - 1))) \<and> l = map (\<lambda>(P, s). (LanguageCon.com.Seq P c2, s)) lc1 @ lc2"
            have f2: "i < length l \<and> fst (l ! i) = c2 \<and> (\<forall>n. \<not> n < i \<or> fst (l ! n) \<noteq> c2)"
              using a0 by blast
            have f3: "(LanguageCon.com.Seq (fst (lc1 ! i)) c2, snd (lc1 ! i)) = lift c2 (lc1 ! i)"
              by (simp add: case_prod_unfold lift_def)            
            then have "fst (l ! length lc1) = c2"
              using a1 by (simp add: cpn_def nth_append)
            thus ?thesis
              using f3 f2 by (metis (no_types) nth_append cp_lc1 
                 fst_conv length_map lift_nth linorder_neqE_nat seq_and_if_not_eq(4))
         qed                  
         have lc2_l:"\<forall>j<length lc2. lc2!j=l!(i+j)"
           using cp_lc1 length_c1_map i_map a0
           by (metis nth_append_length_plus)                                                             
         have lc1_not_empty:"lc1 \<noteq> []"
           using cp cp_lc1 unfolding cpn_def by fastforce      
         have lc2_not_empty:"lc2 \<noteq> []"
           using a0 cp_lc1 i_map by auto                      
         have l_is:"s2= snd (last lc1)"
         using cp_lc1 li a0 lc1_not_empty i_map unfolding cpn_def
         by (auto simp add: last_conv_nth lc2_l)       
         let ?m_lc1 = "map (lift c2) lc1"
         (* let ?lm_lc1 = "(length ?m_lc1)"
         let ?last_m_lc1 = "?m_lc1!(?lm_lc1-1)" *)                         
         have last_m_lc1:"l!(i-1) = (Seq (fst (last lc1)) c2,s2)"
         proof -
           have a000:"\<forall>p c. (LanguageCon.com.Seq (fst p) c, snd p) = lift c p"
             using Cons_lift by force
           have "length (map (lift c2) lc1) = i"
               using i_map by fastforce
           then show ?thesis
             by (metis (no_types) One_nat_def l_is a000 cp_lc1 diff_less last_conv_nth last_map 
            lc1_not_empty length_c1_map length_greater_0_conv less_Suc0 nth_append)                       
         qed  
         have last_mcl1_not_F:"snd (last ?m_lc1) \<notin> Fault ` F"                 
         proof -
          have "map (lift c2) lc1 \<noteq> []"
            by (metis lc1_not_empty list.map_disc_iff)
          then show ?thesis
            by (metis (full_types) One_nat_def i_not_fault l_is last_conv_nth last_snd lc1_not_empty li snd_conv)
         qed        
         have map_cp:"(\<Gamma>,?m_lc1) \<in> cpn n \<Gamma> (Seq c1 c2) s"               
         proof -
           have f1: "lc1 ! 0 = (c1, s) \<and> (n,\<Gamma>, lc1) \<in> cptn_mod_nest_call \<and> \<Gamma> = \<Gamma>"
             using cp_lc1 cpn_def by blast
           then have f2: "(n,\<Gamma>, ?m_lc1) \<in> cptn_mod_nest_call" using lc1_not_empty
             by (metis Cons_lift SmallStepCon.nth_tl cptn_mod_nest_call.CptnModNestSeq1)
           then show ?thesis
             using f2 f1 lc1_not_empty by (simp add: cpn_def lift_def)
         qed
         then have map_cp':"(\<Gamma>,?m_lc1) \<in> cp \<Gamma> (Seq c1 c2) s"
           unfolding cpn_def cp_def
           using cptn_eq_cptn_mod_nest by fastforce
         also have map_assum:"(\<Gamma>,?m_lc1) \<in> assum (p,R)" 
           using sub_assum a10 a11 \<Gamma>1 cp_lc1 lc1_not_empty 
           by (metis SmallStepCon.nth_tl map_is_Nil_conv)
         ultimately have "((\<Gamma>,lc1) \<in> assum(p, R))"  
           using \<Gamma>1 assum_map using assum_map cp_lc1' by blast                          
         then have lc1_comm:"(\<Gamma>,lc1) \<in> comm(G, (q,a)) F"  
           using a1 cp_lc1 by (meson IntI com_validityn_def contra_subsetD)
         then have m_lc1_comm:"(\<Gamma>,?m_lc1) \<in> comm(G, (q,a)) F"
           using map_cp' map_assum comm_map cp_lc1' by fastforce         
         then have i_step:"\<Gamma>\<turnstile>\<^sub>c(l!(i-1)) \<rightarrow> (l!i)"
         proof -
           have "\<Gamma>\<turnstile>\<^sub>c(l!(i-1)) \<rightarrow>\<^sub>c\<^sub>e (l!(i))"
           proof -
             have f1: "\<forall>n na. \<not> n < na \<or> Suc (na - Suc n) = na - n"
               by (meson Suc_diff_Suc)
             have "map (lift c2) lc1 \<noteq> []"
               by (metis lc1_not_empty map_is_Nil_conv)
             then have f2: "0 < length (map (lift c2) lc1)"
               by (meson length_greater_0_conv)             
             then have "length (map (lift c2) lc1) - 1 + 1 < length (map (lift c2) lc1 @ lc2)"
               using f2 lc2_not_empty by simp
             then show ?thesis
             using f2 f1
              proof -
                have "0 < i"
                  using f2 i_map by blast
                then show ?thesis
                  by (metis (no_types) One_nat_def Suc_diff_1 a0 add.right_neutral add_Suc_right cp cptn_tran_ce_i)
              qed 
           qed 
           moreover have "\<not>\<Gamma>\<turnstile>\<^sub>c(l!(i-1)) \<rightarrow>\<^sub>e (l!i)"           
             using li last_m_lc1
             by (metis (no_types, lifting) env_c_c' seq_and_if_not_eq(4))
           ultimately show ?thesis using step_ce_elim_cases by blast
         qed         
         then have step:"\<Gamma>\<turnstile>\<^sub>c(Seq (fst (last lc1)) c2,s2) \<rightarrow> (c2, s2)"
           using last_m_lc1  li by fastforce
         then obtain s2' where 
           last_lc1:"fst (last lc1) = Skip \<or> 
            fst (last lc1) = Throw \<and> (s2 = Normal s2')" 
           using seq_skip_throw by blast    
         have final:"final (last lc1)" 
           using last_lc1 l_is unfolding final_def by auto
(* look here for the property *******************************************************************************)
         have normal_last:"fst (last lc1) = Skip \<and> snd (last lc1) \<in> Normal ` q \<or>
                        fst (last lc1) = Throw \<and> snd (last lc1) \<in> Normal ` (a)" 
         proof -         
           have "snd (last lc1) \<notin> Fault ` F"
             using i_not_fault l_is li by auto
           then show ?thesis
             using final comm_dest2 lc1_comm by blast
         qed
         obtain s2' where lastlc1_normal:"snd (last lc1) = Normal s2'" 
           using normal_last by blast
         then have Normals2:"s2 = Normal s2'" by (simp add: l_is ) 
         have Gs2':"(Normal s2', Normal s2')\<in>G" using a5 by auto                     
         have concl:
           "(\<forall>i. Suc i<length l \<longrightarrow> 
           \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow>                                    
             (snd(l!i), snd(l!(Suc i))) \<in> G)"
         proof-
         { fix k 
           assume a00:"Suc k<length l" and
            a21:"\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))" 
            have i_m_l:"\<forall>j <i . l!j = ?m_lc1!j"             
            proof -
              have "map (lift c2) lc1 \<noteq> []"
                by (meson lc1_not_empty list.map_disc_iff)
              then show ?thesis 
                using cp_lc1 i_map length_c1_map by (fastforce simp:nth_append)              
            qed 
            have "(snd(l!k), snd(l!(Suc k))) \<in> G"
            proof (cases "Suc k< i")
              case True 
              then have a11': "\<Gamma>\<turnstile>\<^sub>c(?m_lc1!k)  \<rightarrow> (?m_lc1!(Suc k))" 
                using a11 i_m_l True
              proof -
                have "\<forall>n na. \<not> 0 < n - Suc na \<or> na < n "
                  using diff_Suc_eq_diff_pred zero_less_diff by presburger
                then show ?thesis using True a21 i_m_l by force                  
              qed                                                             
              have "Suc k < length ?m_lc1" using True i_map length_c1_map by metis
              then have "(snd(?m_lc1!k), snd(?m_lc1!(Suc k))) \<in> G"
              using a11' last_mcl1_not_F  m_lc1_comm True i_map length_c1_map 
                    comm_dest1[of \<Gamma>]
                by blast
              thus ?thesis using i_m_l using True by fastforce 
            next
              case False                                            
              have "(Suc k=i) \<or> (Suc k>i)" using False by auto
              thus ?thesis 
              proof
              { assume suck:"(Suc k=i)" 
                then have k:"k=i-1" by auto                                                            
                then show "(snd (l!k), snd (l!Suc k)) \<in> G"               
                proof -
                  have "snd (l!Suc k) = Normal s2'" 
                    using Normals2 suck li by auto     
                  moreover have "snd (l ! k) = Normal s2'"   
                    using Normals2 k last_m_lc1 by fastforce                 
                  moreover have "\<exists>p. p \<in> G "
                    by (meson  case_prod_conv mem_Collect_eq Gs2')
                  ultimately show ?thesis using suck k Normals2
                    using Gs2'  by force                       
                qed
              }
              next
              { 
                assume a001:"Suc k>i"
                then have k:"k\<ge>i" by fastforce
                then obtain k' where k':"k=i+k'" 
                  using add.commute le_Suc_ex by blast
                {assume throw:"c2=Throw \<and> fst (last lc1) = Throw"
                 then have s2_in:"s2' \<in> a" 
                   using Normals2 i_map normal_last li lastlc1_normal 
                   using image_iff snd_conv xstate.inject(1) by auto
                
                 then have "\<forall>k. k\<ge>i \<and> (Suc k < length l) \<longrightarrow> 
                            \<not>(\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
                  using Normals2 li lastlc1_normal a21 a001 a00 a4
                        a0 throw env_tran_right only_one_component_tran_j snd_conv 
                   by (metis  cp env_tran_right)
                  then have ?thesis using a21 a001 k a00 by blast                                  
                }  note left=this
                {assume "\<not>(c2=Throw \<and> fst (last lc1) = Throw)"
                 then have "fst (last lc1) = Skip"
                   using last_m_lc1 last_lc1
                   by (metis step a0 l_is li prod.collapse stepc_Normal_elim_cases(11) stepc_Normal_elim_cases(5))                 
                 then have s2_normal:"s2 \<in> Normal ` q" 
                   using normal_last lastlc1_normal Normals2
                   by fastforce
                 have length_lc2:"length l=i+length lc2" 
                       using i_map cp_lc1 by fastforce
                 have "(\<Gamma>,lc2) \<in>  assum (q,R)" 
                 proof -
                   have left:"snd (lc2!0) \<in> Normal ` q" 
                     using li lc2_l s2_normal lc2_not_empty by fastforce 
                   {
                     fix j
                     assume j_len:"Suc j<length lc2" and
                            j_step:"\<Gamma>\<turnstile>\<^sub>c(lc2!j)  \<rightarrow>\<^sub>e (lc2!(Suc j))"
                     
                     then have suc_len:"Suc (i + j)<length l" using j_len length_lc2
                       by fastforce
                     also then have "\<Gamma>\<turnstile>\<^sub>c(l!(i+j))  \<rightarrow>\<^sub>e (l! (Suc (i+ j)))"
                        using lc2_l j_step j_len by fastforce
                     ultimately have "(snd(lc2!j), snd(lc2!(Suc j))) \<in> R"
                        using assum suc_len lc2_l j_len cp by fastforce 
                   }
                   then show ?thesis using left 
                     unfolding assum_def by fastforce
                 qed
                 also have "(\<Gamma>,lc2) \<in> cpn n \<Gamma> c2 s2"
                   using cp_lc1 i_map l_is last_conv_nth lc1_not_empty by fastforce                 
                 ultimately have comm_lc2:"(\<Gamma>,lc2) \<in>  comm (G, (r,a)) F"
                   using a3 unfolding com_validityn_def by auto
                 have lc2_last_f:"snd (last lc2)\<notin> Fault ` F" 
                   using lc2_l lc2_not_empty l_f cp_lc1 by fastforce
                 have suck':"Suc k' < length lc2" 
                   using k' a00 length_lc2 by arith
                 moreover then have "\<Gamma>\<turnstile>\<^sub>c(lc2!k')  \<rightarrow> (lc2!(Suc k'))"  
                   using k' lc2_l a21 by fastforce
                 ultimately have "(snd (lc2! k'), snd (lc2 ! Suc k')) \<in> G"
                   using comm_lc2 lc2_last_f comm_dest1[of \<Gamma> lc2 G r a F k'] 
                   by blast
                 then have ?thesis using suck' lc2_l k' by fastforce
                }                    
                then show ?thesis using left by auto                 
              }
              qed 
            qed
          } thus ?thesis by auto 
         qed note left=this
         have right:"(final (last l)  \<longrightarrow>                    
                   ((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal `  r)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` a))"
         proof -
         { assume final_l:"final (last l)" 
           have eq_last_lc2_l:"last l=last lc2" by (simp add: cp_lc1 lc2_not_empty)
           then have final_lc2:"final (last lc2)" using final_l by auto
           {
             assume lst_lc1_throw:"fst (last lc1) = Throw"                        
             then have c2_throw:"c2 = Throw" 
               using lst_lc1_throw step lastlc1_normal stepc_elim_cases_Seq_skip_c2
               by fastforce                                                                  
             have s2_a:"s2 \<in> Normal ` (a)"
               using normal_last 
               by (simp add: lst_lc1_throw l_is)
             have all_ev:"\<forall>k<length l - 1. k\<ge>i \<and> (Suc k < length l) \<longrightarrow> 
                            \<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))"
             proof -
               have s2_in:"s2' \<in> a" 
                 using Normals2 i_map normal_last li lastlc1_normal 
                 using image_iff snd_conv xstate.inject(1) lst_lc1_throw by auto
               then have "\<forall>k. k\<ge>i \<and> (Suc k < length l) \<longrightarrow> 
                            \<not>(\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
                 using Normals2 li lastlc1_normal   a4
                     a0 c2_throw env_tran_right only_one_component_tran_j snd_conv 
                 by (metis  cp env_tran_right)  
               thus ?thesis by (metis Suc_eq_plus1 cp cptn_tran_ce_i step_ce_elim_cases)      
             qed    
             then have Throw:"fst (l!(length l - 1)) = Throw"
             using cp c2_throw a0 cptn_i_env_same_prog[of \<Gamma> l "((length l)-1)" i] 
               by fastforce                            
             then have "snd (l!(length l - 1)) \<in> Normal ` (a) \<and> fst (l!(length l - 1)) = Throw"
               using  all_ev a0 s2_a li a4 env_tran_right stability[of a R l i "(length l) -1" _ \<Gamma>] Throw 
               by (metis One_nat_def Suc_pred length_greater_0_conv 
                         lessI linorder_not_less list.size(3) 
                         not_less0 not_less_eq_eq snd_conv)                              
             then have "((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal `  r)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (a))" 
              using a0 by (metis last_conv_nth list.size(3) not_less0)                           
          }  note left = this
          {  assume "fst (last lc1) = Skip"                 
             then have s2_normal:"s2 \<in> Normal ` q" 
               using normal_last lastlc1_normal Normals2
               by fastforce
             have length_lc2:"length l=i+length lc2" 
                   using i_map cp_lc1 by fastforce
             have "(\<Gamma>,lc2) \<in>  assum (q,R)" 
             proof -
               have left:"snd (lc2!0) \<in> Normal ` q" 
                 using li lc2_l s2_normal lc2_not_empty by fastforce 
               {
                 fix j
                 assume j_len:"Suc j<length lc2" and
                        j_step:"\<Gamma>\<turnstile>\<^sub>c(lc2!j)  \<rightarrow>\<^sub>e (lc2!(Suc j))"                 
                 then have suc_len:"Suc (i + j)<length l" using j_len length_lc2
                   by fastforce
                 also then have "\<Gamma>\<turnstile>\<^sub>c(l!(i+j))  \<rightarrow>\<^sub>e (l! (Suc (i+ j)))"
                    using lc2_l j_step j_len by fastforce
                 ultimately have "(snd(lc2!j), snd(lc2!(Suc j))) \<in> R"
                    using assum suc_len lc2_l j_len cp by fastforce 
               }
               then show ?thesis using left 
                 unfolding assum_def by fastforce
             qed
             also have "(\<Gamma>,lc2) \<in> cpn n \<Gamma> c2 s2"
               using cp_lc1 i_map l_is last_conv_nth lc1_not_empty by fastforce
             ultimately have comm_lc2:"(\<Gamma>,lc2) \<in>  comm (G, (r,a)) F"
               using a3 unfolding com_validityn_def by auto
             have lc2_last_f:"snd (last lc2)\<notin> Fault ` F" 
               using lc2_l lc2_not_empty l_f cp_lc1 by fastforce             
             then have "((fst (last lc2) = Skip \<and> 
                    snd (last lc2) \<in> Normal `  r)) \<or>
                    (fst (last lc2) = Throw \<and> 
                    snd (last lc2) \<in> Normal ` a)" 
             using final_lc2 comm_lc2 unfolding comm_def by auto
             then have "((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal `  r)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` a)" 
             using eq_last_lc2_l by auto
          }
          then have "((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` r)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` a)" 
            using left using last_lc1 by auto
        } thus ?thesis by auto qed         
     thus ?thesis using left l_f \<Gamma>1 unfolding comm_def by force       
       qed             
     } thus ?thesis using \<Gamma>1 unfolding comm_def by auto qed
   } thus ?thesis by auto qed 
 } thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed

lemma Catch_env_P:assumes a0:"\<Gamma>\<turnstile>\<^sub>c(Catch P Q,s) \<rightarrow>\<^sub>e (Catch P Q,t)"
      shows "\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow>\<^sub>e (P,t)"
using a0
by (metis env_not_normal_s snormal_enviroment)

lemma map_catch_eq_state:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Catch c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift_catch c2) l2"
shows
  "\<forall>i<length l1. snd (l1!i) = snd (l2!i)"
using a0 a1 a2 unfolding cp_def
by (simp add: snd_lift_catch) 

lemma map_eq_catch_c:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Catch c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift_catch c2) l2"
shows
  "\<forall>i<length l1. fst (l1!i) = Catch (fst (l2!i)) c2"
proof -
  {fix i
  assume a3:"i<length l1"
  have "fst (l1!i) = Catch (fst (l2!i)) c2"
  using a0 a1 a2 a3 unfolding lift_catch_def
    by (simp add: case_prod_unfold) 
  }thus ?thesis by auto
qed 

lemma same_env_catch_c:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Catch c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift_catch c2) l2"
shows
"\<forall>i. Suc i<length l2 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l2!i)  \<rightarrow>\<^sub>e (l2!(Suc i)) = 
            \<Gamma>\<turnstile>\<^sub>c(l1!i)  \<rightarrow>\<^sub>e (l1!(Suc i))" 
proof -
  have a0a:"(\<Gamma>,l1) \<in>cptn \<and> l1!0 = ((Catch c1 c2),s)" 
    using a0 unfolding cp_def by blast
  have a1a: "(\<Gamma>,l2) \<in>cptn \<and> l2!0 = (c1,s)"
    using a1 unfolding cp_def by blast
  {
    fix i
    assume a3:"Suc i< length l2"
    have "\<Gamma>\<turnstile>\<^sub>c(l2!i)  \<rightarrow>\<^sub>e (l2!(Suc i)) = 
            \<Gamma>\<turnstile>\<^sub>c(l1!i)  \<rightarrow>\<^sub>e (l1!(Suc i))"
    proof
    {
      assume a4:"\<Gamma>\<turnstile>\<^sub>c l2 ! i \<rightarrow>\<^sub>e l2 ! Suc i"
      obtain c1i s1i c1si s1si where l1prod:"l1 ! i=(c1i,s1i) \<and> l1!Suc i = (c1si,s1si)"
        by fastforce
      obtain c2i s2i c2si s2si where l2prod:"l2 ! i=(c2i,s2i) \<and> l2!Suc i = (c2si,s2si)"
        by fastforce
      then have "c1i = (Catch c2i c2) \<and> c1si = (Catch c2si c2)"
        using  a0 a1 a2 a3 a4  l1prod 
        by (simp add: lift_catch_def)         
      also have "s2i=s1i \<and> s2si=s1si"
        using  a0 a1 a4  a2 a3 l2prod  l1prod
        by (simp add: lift_catch_def)         
      ultimately show "\<Gamma>\<turnstile>\<^sub>c l1 ! i \<rightarrow>\<^sub>e (l1 ! Suc i)" 
        using a4 l1prod l2prod
        by (metis Env_n env_c_c' env_not_normal_s step_e.Env)
    } 
    {
      assume a4:"\<Gamma>\<turnstile>\<^sub>c l1 ! i \<rightarrow>\<^sub>e l1 ! Suc i"
      obtain c1i s1i c1si s1si where l1prod:"l1 ! i=(c1i,s1i) \<and> l1!Suc i = (c1si,s1si)"
        by fastforce
      obtain c2i s2i c2si s2si where l2prod:"l2 ! i=(c2i,s2i) \<and> l2!Suc i = (c2si,s2si)"
        by fastforce
      then have "c1i = (Catch c2i c2) \<and> c1si = (Catch c2si c2)"
        using  a0 a1 a2 a3 a4  l1prod
        by (simp add: lift_catch_def)
      also have "s2i=s1i \<and> s2si=s1si"
        using  a0 a1 a4  a2 a3 l2prod l1prod
        by (simp add: lift_catch_def)      
      ultimately show "\<Gamma>\<turnstile>\<^sub>c l2 ! i \<rightarrow>\<^sub>e (l2 ! Suc i)" 
        using a4 l1prod l2prod       
        by (metis Env_n LanguageCon.com.inject(9) env_c_c' env_not_normal_s step_e.Env)   
    }
    qed
   } 
  thus ?thesis by auto
qed


lemma same_comp_catch_c:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Catch c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift_catch c2) l2"
shows
"\<forall>i. Suc i<length l2 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l2!i)  \<rightarrow> (l2!(Suc i)) = 
            \<Gamma>\<turnstile>\<^sub>c(l1!i)  \<rightarrow> (l1!(Suc i))" 
proof -
  have a0a:"(\<Gamma>,l1) \<in>cptn \<and> l1!0 = ((Catch c1 c2),s)" 
    using a0 unfolding cp_def by blast
  have a1a: "(\<Gamma>,l2) \<in>cptn \<and> l2!0 = (c1,s)"
    using a1 unfolding cp_def by blast
  {
    fix i
    assume a3:"Suc i< length l2"
    have "\<Gamma>\<turnstile>\<^sub>c(l2!i)  \<rightarrow> (l2!(Suc i)) = 
            \<Gamma>\<turnstile>\<^sub>c(l1!i)  \<rightarrow> (l1!(Suc i))"
    proof
    {
      assume a4:"\<Gamma>\<turnstile>\<^sub>c l2 ! i \<rightarrow> l2 ! Suc i"
      obtain c1i s1i c1si s1si where l1prod:"l1 ! i=(c1i,s1i) \<and> l1!Suc i = (c1si,s1si)"
        by fastforce
      obtain c2i s2i c2si s2si where l2prod:"l2 ! i=(c2i,s2i) \<and> l2!Suc i = (c2si,s2si)"
        by fastforce
      then have "c1i = (Catch c2i c2) \<and> c1si = (Catch c2si c2)"
        using  a0 a1 a2 a3 a4  map_eq_catch_c l1prod
        by (simp add: lift_catch_def)
      also have "s2i=s1i \<and> s2si=s1si"
        using  a0 a1 a4  a2 a3 l2prod map_eq_state l1prod
        by (simp add: lift_catch_def)          
      ultimately show "\<Gamma>\<turnstile>\<^sub>c l1 ! i \<rightarrow> (l1 ! Suc i)" 
        using a4 l1prod l2prod
        by (simp add: Catchc)        
    } 
    {
      assume a4:"\<Gamma>\<turnstile>\<^sub>c l1 ! i \<rightarrow> l1 ! Suc i"
      obtain c1i s1i c1si s1si where l1prod:"l1 ! i=(c1i,s1i) \<and> l1!Suc i = (c1si,s1si)"
        by fastforce
      obtain c2i s2i c2si s2si where l2prod:"l2 ! i=(c2i,s2i) \<and> l2!Suc i = (c2si,s2si)"
        by fastforce
      then have "c1i = (Catch c2i c2) \<and> c1si = (Catch c2si c2)"
        using  a0 a1 a2 a3 a4  l1prod
       by (simp add: lift_catch_def)          
      also have "s2i=s1i \<and> s2si=s1si"
        using  a0 a1 a4  a2 a3 l2prod  l1prod
        by (simp add: lift_catch_def)          
      ultimately show "\<Gamma>\<turnstile>\<^sub>c l2 ! i \<rightarrow> (l2 ! Suc i)" 
        using a4 l1prod l2prod stepc_elim_cases_Catch_Catch Catch_not_c
        by (metis (no_types))
    }
    qed
   } 
  thus ?thesis by auto
qed

lemma assum_map_catch:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Catch c1 c2) s) \<and> ((\<Gamma>,l1) \<in> assum(p, R))" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift_catch c2) l2"  
shows
  "((\<Gamma>,l2) \<in> assum(p, R))"
proof -
  have a3: "\<forall>i. Suc i<length l2 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l2!i)  \<rightarrow>\<^sub>e (l2!(Suc i)) = 
            \<Gamma>\<turnstile>\<^sub>c(l1!i)  \<rightarrow>\<^sub>e (l1!(Suc i))" 
    using a0 a1 a2 same_env_catch_c by fastforce
  have pair_\<Gamma>l1:"fst (\<Gamma>,l1) = \<Gamma> \<and> snd (\<Gamma>,l1) = l1" by fastforce
  have pair_\<Gamma>l2:"fst (\<Gamma>,l2) = \<Gamma> \<and> snd (\<Gamma>,l2) = l2" by fastforce
  have drop_k_s:"l2!0 = (c1,s)" using a1 cp_def by blast
  have eq_length:"length l1 = length l2" using a2 by auto
  obtain s' where normal_s:"s = Normal s'" 
    using  a0  unfolding cp_def   assum_def  by fastforce
  then have p1:"s'\<in>p" using a0 unfolding cp_def assum_def by fastforce  
  show ?thesis 
  proof -    
    let ?c= "(\<Gamma>,l2)"
    have l:"snd((snd ?c!0)) \<in> Normal ` (p)"
     using p1 drop_k_s a1 normal_s unfolding cp_def by auto
    {fix i
     assume a00:"Suc i<length (snd ?c)" 
     assume a11:"(fst ?c)\<turnstile>\<^sub>c((snd ?c)!i)  \<rightarrow>\<^sub>e ((snd ?c)!(Suc i))"
     have "(snd((snd ?c)!i), snd((snd ?c)!(Suc i))) \<in> R"
     using a0 a1 a2 a3 map_catch_eq_state unfolding assum_def 
     using a00 a11 eq_length by fastforce
    } thus "(\<Gamma>, l2) \<in> assum (p, R)" 
      using l unfolding assum_def by fastforce  
  qed  
qed

lemma comm_map'_catch:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Catch c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) \<and> (\<Gamma>, l2)\<in> comm(G, (q,a)) F" and
  a2:"l1=map (lift_catch c2) l2" 
shows
  "snd (last l1) \<notin> Fault ` F  \<longrightarrow>(Suc k < length l1 \<longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c(l1!k)  \<rightarrow> (l1!(Suc k)) \<longrightarrow>        
       (snd(l1!k), snd(l1!(Suc k))) \<in> G) \<and> 
   (fst (last l1) = (Catch c c2) \<and> final (c, snd (last l1)) \<longrightarrow>     
      (fst (last l1) = (Catch Skip c2) \<and> 
        (snd (last  l1) \<in> Normal ` q) \<or>
      (fst (last l1) = (Catch Throw c2) \<and> 
        snd (last l1) \<in> Normal ` (a))))
     "
proof -
  have a3:"\<forall>i. Suc i<length l2 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l2!i)  \<rightarrow> (l2!(Suc i)) = 
            \<Gamma>\<turnstile>\<^sub>c(l1!i)  \<rightarrow> (l1!(Suc i))" 
    using a0 a1 a2 same_comp_catch_c
    by fastforce
  have pair_\<Gamma>l1:"fst (\<Gamma>,l1) = \<Gamma> \<and> snd (\<Gamma>,l1) = l1" by fastforce
  have pair_\<Gamma>l2:"fst (\<Gamma>,l2) = \<Gamma> \<and> snd (\<Gamma>,l2) = l2" by fastforce
  have drop_k_s:"l2!0 = (c1,s)" using a1 cp_def by blast
  have eq_length:"length l1 = length l2" using a2 by auto
  have len0:"length l2>0" using a1 unfolding cp_def 
      using cptn.simps  by fastforce   
  then have len0:"length l1>0" using eq_length by auto
  then have l1_not_empty:"l1\<noteq>[]" by auto
  then have l2_not_empty:"l2 \<noteq> []" using a2 by blast       
   have last_lenl1:"last l1 = l1!((length l1) -1)" 
        using last_conv_nth l1_not_empty by auto
  have last_lenl2:"last l2 = l2!((length l2) -1)" 
       using last_conv_nth l2_not_empty by auto 
  have a03:"snd (last l2) \<notin> Fault ` F  \<longrightarrow>(\<forall>i ns ns'.                 
               Suc i<length (snd (\<Gamma>, l2)) \<longrightarrow> 
               fst (\<Gamma>, l2)\<turnstile>\<^sub>c((snd (\<Gamma>, l2))!i)  \<rightarrow> ((snd (\<Gamma>, l2))!(Suc i)) \<longrightarrow>                               
                 (snd((snd (\<Gamma>, l2))!i), snd((snd (\<Gamma>, l2))!(Suc i))) \<in> G) \<and> 
               (final (last (snd (\<Gamma>, l2)))  \<longrightarrow>                 
                  ((fst (last (snd (\<Gamma>, l2))) = Skip \<and> 
                    snd (last (snd (\<Gamma>, l2))) \<in> Normal ` q)) \<or>
                  (fst (last (snd (\<Gamma>, l2))) = Throw \<and> 
                    snd (last (snd (\<Gamma>, l2))) \<in> Normal ` (a)))"
  using a1 unfolding comm_def by fastforce
  show ?thesis unfolding comm_def 
  proof -
  { fix k ns ns'
    assume a00a:"snd (last l1) \<notin> Fault ` F"
    assume a00:"Suc k < length l1"    
    then have "k \<le> length l1" using a2 by fastforce    
    have a00:"Suc k < length l2" using eq_length a00 by fastforce
    then have a00a:"snd (last l2) \<notin> Fault ` F"
    proof-
      have "snd (l1!((length l1) -1)) = snd (l2!((length l2) -1))"      
        using a2 a1 a0  map_catch_eq_state eq_length l2_not_empty last_snd 
        by fastforce 
      then have "snd(last l2) = snd (last l1)"
        using last_lenl1 last_lenl2 by auto
      thus ?thesis using a00a by auto
    qed
    then have "snd (last l1) \<notin> Fault ` F \<longrightarrow>\<Gamma>\<turnstile>\<^sub>c(l1!k)  \<rightarrow> (l1!(Suc k)) \<longrightarrow>       
      (snd((snd (\<Gamma>, l1))!k), snd((snd (\<Gamma>, l1))!(Suc k))) \<in> G"
    using  pair_\<Gamma>l1 pair_\<Gamma>l2 a00  a03 a3  eq_length a00a
     by (metis Suc_lessD a0 a1 a2 map_catch_eq_state)
  } note l=this
  {
    assume a00: "fst (last l1) = (Catch c c2) \<and> final (c, snd (last l1))" and
           a01:"snd (last (l1)) \<notin> Fault ` F"
    then have c:"c=Skip \<or> c = Throw"
     unfolding final_def by auto    
    then have fst_last_l2:"fst (last l2) = c"                               
      using  last_lenl1 a00 l1_not_empty eq_length len0 a2 last_conv_nth last_lift_catch 
      by fastforce      
    also have last_eq:"snd (last l2) = snd (last l1)"      
      using l2_not_empty a2 last_conv_nth last_lenl1 last_snd_catch
      by fastforce
    ultimately have "final (fst (last l2),snd (last l2))" 
     using a00 by auto
    then have "final (last l2)" by auto
    also have "snd (last (l2)) \<notin> Fault ` F"
       using  last_eq a01 by auto
    ultimately have "(fst (last  l2)) = Skip \<and> 
                    snd (last  l2) \<in> Normal ` q \<or>
                  (fst (last l2) = Throw \<and> 
                    snd (last l2) \<in> Normal ` (a))"
    using a03 by auto
    then have "(fst (last l1) = (Catch Skip c2) \<and> 
                    snd (last  l1) \<in> Normal ` q) \<or>
                  (fst (last l1) = (Catch Throw c2) \<and> 
                    snd (last l1) \<in> Normal ` (a))"
    using last_eq fst_last_l2 a00 by force
  }
  thus ?thesis using l by auto qed
qed

lemma comm_map''_catch:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Catch c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) \<and> (\<Gamma>, l2)\<in> comm(G, (q,a)) F" and
  a2:"l1=map (lift_catch c2) l2" 
shows
  "snd (last l1) \<notin> Fault ` F \<longrightarrow> ((Suc k < length l1 \<longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c(l1!k)  \<rightarrow> (l1!(Suc k)) \<longrightarrow>        
       (snd(l1!k), snd(l1!(Suc k))) \<in>  G) \<and> 
   (final (last l1) \<longrightarrow>     
      (fst (last l1) = Skip \<and> 
        (snd (last  l1) \<in> Normal ` r) \<or>
      (fst (last l1) = Throw \<and> 
        snd (last l1) \<in> Normal ` a))))
     "
proof -
  have a3:"\<forall>i. Suc i<length l2 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l2!i)  \<rightarrow> (l2!(Suc i)) = 
            \<Gamma>\<turnstile>\<^sub>c(l1!i)  \<rightarrow> (l1!(Suc i))" 
    using a0 a1 a2 same_comp_catch_c
    by fastforce
  have pair_\<Gamma>l1:"fst (\<Gamma>,l1) = \<Gamma> \<and> snd (\<Gamma>,l1) = l1" by fastforce
  have pair_\<Gamma>l2:"fst (\<Gamma>,l2) = \<Gamma> \<and> snd (\<Gamma>,l2) = l2" by fastforce
  have drop_k_s:"l2!0 = (c1,s)" using a1 cp_def by blast
   have eq_length:"length l1 = length l2" using a2 by auto
  have len0:"length l2>0" using a1 unfolding cp_def 
      using cptn.simps  by fastforce   
  then have len0:"length l1>0" using eq_length by auto
  then have l1_not_empty:"l1\<noteq>[]" by auto
  then have l2_not_empty:"l2 \<noteq> []" using a2 by blast       
  have last_lenl1:"last l1 = l1!((length l1) -1)" 
        using last_conv_nth l1_not_empty by auto
  have last_lenl2:"last l2 = l2!((length l2) -1)" 
       using last_conv_nth l2_not_empty by auto 
  have a03:"snd (last l2) \<notin> Fault ` F \<longrightarrow>(\<forall>i ns ns'.                 
               Suc i<length (snd (\<Gamma>, l2)) \<longrightarrow> 
               fst (\<Gamma>, l2)\<turnstile>\<^sub>c((snd (\<Gamma>, l2))!i)  \<rightarrow> ((snd (\<Gamma>, l2))!(Suc i)) \<longrightarrow>                                              
                 (snd((snd (\<Gamma>, l2))!i), snd((snd (\<Gamma>, l2))!(Suc i))) \<in> G) \<and> 
               (final (last (snd (\<Gamma>, l2)))  \<longrightarrow>                 
                  ((fst (last (snd (\<Gamma>, l2))) = Skip \<and> 
                    snd (last (snd (\<Gamma>, l2))) \<in> Normal ` q)) \<or>
                  (fst (last (snd (\<Gamma>, l2))) = Throw \<and> 
                    snd (last (snd (\<Gamma>, l2))) \<in> Normal ` (a)))"
  using a1 unfolding comm_def by fastforce
  show ?thesis unfolding comm_def 
  proof -
  { fix k ns ns'
    assume a00a:"snd (last l1) \<notin> Fault ` F"
    assume a00:"Suc k < length l1"    
    then have "k \<le> length l1" using a2 by fastforce    
    have a00:"Suc k < length l2" using eq_length a00 by fastforce   
    then have a00a:"snd (last l2) \<notin> Fault ` F"
    proof-
      have "snd (l1!((length l1) -1)) = snd (l2!((length l2) -1))"      
        using a2 a1 a0  map_catch_eq_state eq_length l2_not_empty last_snd 
        by fastforce 
      then have "snd(last l2) = snd (last l1)"
        using last_lenl1 last_lenl2 by auto
      thus ?thesis using a00a by auto
    qed 
    then have "\<Gamma>\<turnstile>\<^sub>c(l1!k)  \<rightarrow> (l1!(Suc k)) \<longrightarrow>          
        (snd((snd (\<Gamma>, l1))!k), snd((snd (\<Gamma>, l1))!(Suc k))) \<in> G"
       using  pair_\<Gamma>l1 pair_\<Gamma>l2 a00  a03 a3  eq_length a00a
      by (metis (no_types,lifting) a2 Suc_lessD nth_map snd_lift_catch)
    } note l= this
    {
     assume a00: "final (last l1)"           
     then have c:"fst (last l1)=Skip \<or> fst (last l1) = Throw"
       unfolding final_def by auto 
     moreover have "fst (last l1) = Catch (fst (last l2)) c2" 
       using a2 last_lenl1 eq_length
      proof -
        have "last l2 = l2 ! (length l2 - 1)"
          using l2_not_empty last_conv_nth by blast
        then show ?thesis
          by (metis One_nat_def a2 l2_not_empty last_lenl1 last_lift_catch)
      qed
      ultimately have False by simp  
    } thus ?thesis using l  by auto qed
qed

lemma comm_map_catch:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Catch c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) \<and> (\<Gamma>, l2)\<in> comm(G, (q,a)) F" and
  a2:"l1=map (lift_catch c2) l2" 
shows
  "(\<Gamma>, l1)\<in> comm(G, (r,a)) F"
proof - 
  {fix i ns ns'
   have "snd (last l1) \<notin> Fault ` F  \<longrightarrow>(Suc i < length (l1) \<longrightarrow>
        \<Gamma>\<turnstile>\<^sub>c (l1 ! i) \<rightarrow> (l1 ! (Suc i)) \<longrightarrow>       
        (snd (l1 ! i), snd (l1 ! Suc i)) \<in> G) \<and>
        (SmallStepCon.final (last l1) \<longrightarrow>                  
                   fst (last l1) = LanguageCon.com.Skip \<and>
                   snd (last l1) \<in> Normal ` r \<or>
                   fst (last l1) = LanguageCon.com.Throw \<and>
                   snd (last l1) \<in> Normal ` a) "
      using comm_map''_catch[of \<Gamma> l1 c1 c2 s l2 G q a F i r] a0 a1 a2 
      by fastforce
   }  then show ?thesis using comm_def unfolding comm_def by force       
qed

lemma Catch_sound1: 
assumes
  a0:"(n,\<Gamma>,x)\<in>cptn_mod_nest_call" and
  a1:"x!0 = ((Catch P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"\<not> final (last x)" and
  a4:"env_tran_right \<Gamma> x rely"
shows
  "\<exists>xs. (\<Gamma>,xs) \<in> cpn n \<Gamma> P s \<and> x = map (lift_catch Q) xs"
using a0 a1 a2 a3 a4
proof (induct arbitrary: P s)
  case (CptnModNestOne n \<Gamma> C s1)
  then have "(\<Gamma>, [(P,s)]) \<in> cpn n \<Gamma> P s \<and> [(C, s1)] = map (lift_catch Q) [(P,s)]"
    unfolding cpn_def lift_catch_def
    by (simp add: cptn_mod_nest_call.CptnModNestOne) 
  thus ?case by fastforce
next
  case (CptnModNestEnv \<Gamma> C s1 t1 n xsa)
  then have C:"C=Catch P Q" unfolding lift_catch_def by fastforce
  have "\<exists>xs. (\<Gamma>, xs) \<in> cpn n \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift_catch Q) xs"
  proof -
     have "((C, t1) # xsa) ! 0 = (Catch P Q, t1)" using C by auto
     moreover have "\<forall>i<length ((C, t1) # xsa). fst (((C, t1) # xsa) ! i) \<noteq> Q"
       using CptnModNestEnv(5) by fastforce
     moreover have "\<not> SmallStepCon.final (last ((C, t1) # xsa))" using CptnModNestEnv(6) 
       by fastforce
     ultimately show ?thesis
       using CptnModNestEnv(3) CptnModNestEnv(7) env_tran_tail by blast     
  qed 
  then obtain xs where hi:"(\<Gamma>, xs) \<in> cpn n \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift_catch Q) xs"
    by fastforce
  have s1_s:"s1=s" using  CptnModNestEnv unfolding cpn_def by auto
  obtain xsa' where xs:"xs=((P,t1)#xsa') \<and> (n,\<Gamma>,((P,t1)#xsa'))\<in>cptn_mod_nest_call \<and> 
                  (C, t1) # xsa = map (lift_catch Q) ((P,t1)#xsa')" 
    using hi  unfolding cpn_def by fastforce
  
  have env_tran:"\<Gamma>\<turnstile>\<^sub>c(P,s1) \<rightarrow>\<^sub>e (P,t1)" using CptnModNestEnv Catch_env_P by (metis fst_conv nth_Cons_0)  
  then have "(n,\<Gamma>,(P,s1)#(P,t1)#xsa')\<in>cptn_mod_nest_call" using xs env_tran 
    using cptn_mod_nest_call.CptnModNestEnv by blast 
  then have "(\<Gamma>,(P,s1)#(P,t1)#xsa') \<in> cpn n \<Gamma> P s" 
    using cpn_def s1_s by fastforce
  moreover have "(C,s1)#(C, t1) # xsa = map (lift_catch Q) ((P,s1)#(P,t1)#xsa')"
    using xs C unfolding lift_catch_def by fastforce
  ultimately show ?case by auto
next
  case (CptnModNestSkip)
  thus ?case by (metis SmallStepCon.redex_not_Catch fst_conv nth_Cons_0)
next
  case (CptnModNestThrow)
  thus ?case by (metis SmallStepCon.redex_not_Catch fst_conv nth_Cons_0)
next
  case (CptnModNestCatch1 n \<Gamma> P0 sa xsa zs P1)
  then have a1:"LanguageCon.com.Catch P Q = LanguageCon.com.Catch P0 P1"
    by fastforce  
  have f1: "sa = s"
    using CptnModNestCatch1.prems(1) by force
  have f2: "P = P0 \<and> Q = P1" using a1 by auto
  have "(n,\<Gamma>, (P0, sa) # xsa) \<in> cptn_mod_nest_call"
    by (metis CptnModNestCatch1.hyps(1))
  hence "(\<Gamma>, (P0, sa) # xsa) \<in> cpn n \<Gamma> P s"
    using f2 f1 by (simp add: cpn_def)
  thus ?case
    using Cons_lift_catch CptnModNestCatch1.hyps(3) a1 by blast   
next
 case (CptnModNestCatch2 n \<Gamma> P1 sa xsa  ys zs Q1)
  have "final (last ((Skip, sa)# ys))"
  proof -
    have cptn:"(n, \<Gamma>, (Skip,snd (last ((P1, sa) # xsa))) # ys) \<in> cptn_mod_nest_call" 
      using CptnModNestCatch2(4) by (simp add: cptn_eq_cptn_mod_set)
    then have cptn':"(\<Gamma>, (Skip,snd (last ((P1, sa) # xsa))) # ys) \<in> cptn"
      using cptn_eq_cptn_mod_nest by blast       
    moreover have throw_0:"((Skip,snd (last ((P1, sa) # xsa))) # ys)!0 = (Skip, snd (last ((P1, sa) # xsa))) \<and> 0 < length((Skip, snd (last ((P1, sa) # xsa))) # ys)"
      by force         
    moreover have last:"last ((Skip,snd (last ((P1, sa) # xsa))) # ys) = 
                      ((Skip,snd (last ((P1, sa) # xsa))) # ys)!((length ((Skip,snd (last ((P1, sa) # xsa))) # ys)) - 1)"
      using last_conv_nth by auto
    moreover have env_tran:"env_tran_right \<Gamma> ((Skip,snd (last ((P1, sa) # xsa))) # ys) rely" 
      using  CptnModNestCatch2.hyps(6) CptnModNestCatch2.prems(4) env_tran_subl env_tran_tail by blast          
    ultimately obtain st' where "fst (last ((Skip,snd (last ((P1, sa) # xsa))) # ys)) = Skip \<and>        
                     snd (last ((Skip,snd (last ((P1, sa) # xsa))) # ys)) = Normal st'" 
      using  CptnModNestCatch2 zero_skip_all_skip[of \<Gamma> "((Skip,snd (last ((P1, sa) # xsa))) # ys)" "(length ((Skip,snd (last ((P1, sa) # xsa))) # ys))-1"]
      by (metis (no_types, hide_lams) SmallStepCon.final_def append_Cons diff_less fst_conv 
         last_appendR list.simps(3) zero_less_one)      
    thus ?thesis using final_def by (metis fst_conv last.simps)       
  qed
  thus ?case 
    by (metis (no_types, lifting) CptnModNestCatch2.hyps(3) CptnModNestCatch2.hyps(6) 
        CptnModNestCatch2.prems(3) SmallStepCon.final_def append_is_Nil_conv last.simps 
        last_appendR list.simps(3) prod.collapse)     
next
  case (CptnModNestCatch3 n \<Gamma> P0 sa xsa sa' P1 ys zs)
  then have "P0 = P \<and> P1 = Q" by auto
  then obtain i where zs:"fst (zs!i) = Q \<and> (i< (length zs))" 
    using CptnModNestCatch3
    by (metis (no_types, lifting) add_diff_cancel_left' fst_conv length_Cons length_append nth_append_length zero_less_Suc zero_less_diff)    
  then have "Suc i< length ((Catch P0 P1,Normal sa)#zs)" by fastforce
  then have "fst (((Catch P0 P1, Normal sa) # zs)!Suc i) = Q" using zs by fastforce    
  thus ?case using CptnModNestCatch3(9) zs by auto
qed (auto)

lemma Catch_sound2: 
assumes
  a0:"(n,\<Gamma>,x)\<in>cptn_mod_nest_call" and
  a1:"x!0 = ((Catch P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"fst (last x) = Skip" and
  a4:"env_tran_right \<Gamma> x rely"
shows
  "\<exists>xs ys. (\<Gamma>,xs) \<in> cpn n \<Gamma> P s \<and> x = ((map (lift_catch Q) xs)@((Skip,snd(last xs))#ys))"
using a0 a1 a2 a3 a4
proof (induct arbitrary: P s)
  case (CptnModNestOne n \<Gamma> C s1)  
  thus ?case by fastforce
next
  case (CptnModNestEnv \<Gamma> C s1 t1 n xsa)
  then have C:"C=Catch P Q" unfolding lift_catch_def by fastforce
  have "\<exists>xs ys. (\<Gamma>, xs) \<in> cpn n \<Gamma> P t1 \<and> (C, t1) # xsa = 
                map (lift_catch Q) xs@((Skip, snd(last xs))#ys)"
  proof -
     have "((C, t1) # xsa) ! 0 = (LanguageCon.com.Catch P Q, t1)" using C by auto
     moreover have "\<forall>i<length ((C, t1) # xsa). fst (((C, t1) # xsa) ! i) \<noteq> Q"
       using CptnModNestEnv(5) by fastforce
     moreover have "fst (last ((C, t1) # xsa)) = Skip" using CptnModNestEnv(6) 
       by fastforce
     ultimately show ?thesis
       using CptnModNestEnv(3) CptnModNestEnv(7) env_tran_tail by blast    
  qed 
  then obtain xs ys where hi:"(\<Gamma>, xs) \<in> cpn n \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift_catch Q) xs@((Skip,snd(last ((P, t1)#xs)))#ys)"
    by fastforce
  have s1_s:"s1=s" using  CptnModNestEnv unfolding cp_def by auto
  have "\<exists>xsa' ys. xs=((P,t1)#xsa') \<and> (n,\<Gamma>,((P,t1)#xsa'))\<in>cptn_mod_nest_call \<and> (C, t1) # xsa = map (lift_catch Q) ((P,t1)#xsa')@((Skip, snd(last xs))#ys)" 
    using hi  unfolding cp_def
  proof -
      have "(n,\<Gamma>,xs)\<in>cptn_mod_nest_call \<and> xs!0 = (P,t1)" using hi unfolding cpn_def by fastforce
      moreover then have "xs\<noteq>[]" using CptnEmpty calculation by blast      
      moreover  obtain xsa' where "xs=((P,t1)#xsa')" using SmallStepCon.nth_tl calculation by fastforce 
      ultimately show ?thesis
        using hi by auto
  qed
  then obtain xsa' ys where xs:"xs=((P,t1)#xsa') \<and> (n,\<Gamma>,((P,t1)#xsa'))\<in>cptn_mod_nest_call \<and> (C, t1) # xsa = 
                                    map (lift_catch Q) ((P,t1)#xsa')@((Skip,snd(last ((P,s1)#(P,t1)#xsa')))#ys)"
    by fastforce
  have env_tran:"\<Gamma>\<turnstile>\<^sub>c(P,s1) \<rightarrow>\<^sub>e (P,t1)" using CptnModNestEnv Catch_env_P by (metis fst_conv nth_Cons_0)  
  then have "(n,\<Gamma>,(P,s1)#(P,t1)#xsa')\<in>cptn_mod_nest_call" using xs env_tran CptnEnv    
    by (simp add: cptn_mod_nest_call.CptnModNestEnv)   
  then have "(\<Gamma>,(P,s1)#(P,t1)#xsa') \<in> cpn n \<Gamma> P s" 
    using cpn_def s1_s by fastforce
  moreover have "(C,s1)#(C, t1) # xsa = map (lift_catch Q) ((P,s1)#(P,t1)#xsa')@((Skip,snd(last ((P,s1)#(P,t1)#xsa')))#ys)"
    using xs C unfolding lift_catch_def
    by auto
  ultimately show ?case by fastforce 
next
  case (CptnModNestSkip)
  thus ?case by (metis SmallStepCon.redex_not_Catch fst_conv nth_Cons_0)
next
  case (CptnModNestThrow)
  thus ?case by (metis SmallStepCon.redex_not_Catch fst_conv nth_Cons_0)
next
  case (CptnModNestCatch1 n \<Gamma> P0 sa xsa zs P1)  
  thus ?case
  proof -
    have "\<forall>c x. (LanguageCon.com.Catch c P1, x) # zs = map (lift_catch P1) ((c, x) # xsa)"
      using Cons_lift_catch CptnModNestCatch1.hyps(3) by blast
    then have "(P0, sa) # xsa = []"
      by (metis (no_types) CptnModNestCatch1.prems(3) LanguageCon.com.distinct(19) One_nat_def last_conv_nth last_lift_catch map_is_Nil_conv)
    then show ?thesis
      by force
  qed 
next
  case (CptnModNestCatch2 n \<Gamma> P1 sa xsa  ys zs Q1) 
  then have "P1 = P \<and> Q1 = Q \<and> sa = s" by auto  
  moreover then have "(\<Gamma>, (P1,sa) # xsa)\<in> cpn n \<Gamma> P s" 
    using CptnModNestCatch2(1)
    by (simp add: cpn_def cptn_eq_cptn_mod_set)  
  moreover obtain s' where "last zs=(Skip, s')" 
  proof -
    assume a1: "\<And>s'. last zs = (LanguageCon.com.Skip, s') \<Longrightarrow> thesis"
    have "\<exists>x. last zs = (LanguageCon.com.Skip, x)"
      by (metis (no_types) CptnModNestCatch2.hyps(6) CptnModNestCatch2.prems(3) append_is_Nil_conv last_ConsR list.simps(3) prod.exhaust_sel)
    then show ?thesis
      using a1 by metis
  qed        
  ultimately show ?case 
    using Cons_lift_catch_append CptnModNestCatch2.hyps(6)  by fastforce  
next 
  case (CptnModNestCatch3 n \<Gamma> P0 sa xsa sa' P1 ys zs)   
  then have "P0 = P \<and> P1 = Q \<and> s=Normal sa" by auto
  then obtain i where zs:"fst (zs!i) = Q \<and> (i< (length zs))" 
    using CptnModNestCatch3    
    by (metis (no_types, lifting) add_diff_cancel_left' fst_conv length_Cons length_append nth_append_length zero_less_Suc zero_less_diff)    
  then have si:"Suc i< length ((Catch P0 P1,Normal sa)#zs)" by fastforce
  then have "fst (((Seq P0 P1, Normal sa) # zs)!Suc i) = Q" using zs by fastforce    
  thus ?case using CptnModNestCatch3(9) zs
     by (metis si nth_Cons_Suc)
qed (auto)

lemma Catch_sound3: 
assumes
  a0:"(\<Gamma>,x)\<in>cptn" and
  a1:"x!0 = ((Catch P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"fst(last x) = Throw" and
  a4:"env_tran_right \<Gamma> x rely "
shows
  "False"
using a0 a1 a2 a3 a4
proof (induct arbitrary: P s)
  case (CptnOne \<Gamma> C s1) thus ?case by auto
next
  case (CptnEnv \<Gamma> C st t xsa) 
    thus ?case
    proof -
      have f1: "env_tran_right \<Gamma> ((C, t) # xsa) rely"
        using CptnEnv.prems(4) env_tran_tail by blast
      have "LanguageCon.com.Catch P Q = C"
        using CptnEnv.prems(1) by auto
      then show ?thesis
        using f1 CptnEnv.hyps(3) CptnEnv.prems(2) CptnEnv.prems(3) by moura
    qed
next  
  case (CptnComp \<Gamma> C st C' st' xsa)
  then have c_catch:"C = (Catch P Q) \<and> st = s" by force
  from CptnComp show ?case proof(cases)
    case (Catchc P1 P1' P2) thus ?thesis
    proof -
      have f1: "env_tran_right \<Gamma> ((C', st') # xsa) rely"
        using CptnComp.prems(4) env_tran_tail by blast
      have "Q = P2"
        using c_catch Catchc(1)  by blast
      then show ?thesis
        using f1 CptnComp.hyps(3) CptnComp.prems(2) CptnComp.prems(3) Catchc(2) by moura
    qed
  next
    case  (CatchSkipc) thus ?thesis
    proof -
      have "fst (((C', st') # xsa) ! 0) = LanguageCon.com.Skip"
        by (simp add: local.CatchSkipc(2))
      then show ?thesis
        by (metis (no_types) CptnComp.hyps(2) CptnComp.prems(3) LanguageCon.com.distinct(17) 
            last_ConsR last_length length_Cons lessI list.simps(3) zero_skip_all_skip)
    qed    
  next
    case (SeqThrowc C2 s') thus ?thesis
     by (simp add: c_catch)    
  next
     case (FaultPropc) thus ?thesis 
      using c_catch redex_not_Catch by blast 
  next
    case (StuckPropc) thus ?thesis 
      using c_catch redex_not_Catch by blast
  next
    case (AbruptPropc) thus ?thesis 
      using c_catch redex_not_Catch by blast
  qed (auto)
qed

lemma catch_map_xs_ys':
  assumes
  a0:"(n, \<Gamma>, (P0, sa) # xsa) \<in> cptn_mod_nest_call" and    
  a1:"fst (last ((P0, sa) # xsa)) = C" and
  a2:"(n,\<Gamma>, (P1, snd (last ((P0, sa) # xsa))) # ys) \<in> cptn_mod_nest_call" and
  a3:"zs = map (lift_catch P1) xsa @ (P1, snd (last ((P0, sa) # xsa))) # ys" and
  a4:"((LanguageCon.com.Catch P0 P1, sa) # zs) ! 0 = (LanguageCon.com.Catch P Q, s)" and
  a5:"i < length ((LanguageCon.com.Catch P0 P1, sa) # zs) \<and> ((LanguageCon.com.Catch P0 P1, sa) # zs) ! i = (Q, sj)" and
  a6:"\<forall>j<i. fst (((LanguageCon.com.Catch P0 P1, sa) # zs) ! j) \<noteq> Q"
shows 
  "\<exists>xs ys. (\<Gamma>, xs) \<in> cpn n \<Gamma> P s \<and>
            (\<Gamma>, ys) \<in> cpn n \<Gamma> Q (snd (xs ! (i - 1))) \<and> (LanguageCon.com.Catch P0 P1, sa) # zs = map (lift_catch Q) xs @ ys"
proof -
  let ?P0 = "(P0, sa) # xsa"
  have P_Q:"P=P0 \<and> s=sa \<and> Q = P1" using a4 by force
  have i:"i=(length ((P0, sa) # xsa))"   
  proof (cases "i=(length ((P0, sa) # xsa))")
    case True thus ?thesis by auto
  next
    case False     
    then have i:"i<(length ((P0, sa) # xsa)) \<or> i > (length ((P0, sa) # xsa))" by auto
    {
      assume i:"i<(length ((P0, sa) # xsa))"
      then have eq_map:"((LanguageCon.com.Catch P0 P1, sa) # zs) ! i = map (lift_catch P1) ((P0, sa) # xsa) ! i" 
        using a3 Cons_lift_catch_append
        by (metis (no_types, lifting) length_map nth_append) 
      then have  "\<exists>ci si. map (lift_catch P1) ((P0, sa) # xsa) ! i = (Catch ci P1,si)" 
        using i unfolding lift_catch_def
        by (metis a5 eq_map fst_conv length_map map_lift_catch_all_catch)
      then have  "((LanguageCon.com.Catch P0 P1, sa) # zs) ! i \<noteq> (Q, sj)" 
        using P_Q eq_map by fastforce
      then have ?thesis using a5 by auto
    }note l=this
    {
      assume i:"i>(length ((P0, sa) # xsa))"
      have "fst (((LanguageCon.com.Catch P0 P1, sa) # zs) ! (length ?P0)) = Q"
        using a3 P_Q Cons_lift_catch_append by (metis fstI length_map nth_append_length) 
      then have ?thesis using a6 i by auto
    }
    thus ?thesis using l i by auto
   qed
   then have  "(\<Gamma>, (P0, sa) # xsa) \<in> cpn n \<Gamma> P s" 
    using a0  P_Q unfolding cpn_def by fastforce
  also have "(\<Gamma>, (P1, snd (last ((P0, sa) # xsa))) # ys) \<in> cpn n \<Gamma> Q (snd (?P0 ! ((length ?P0) -1)))" 
    using a3 cptn_eq_cptn_mod P_Q unfolding cpn_def
  proof -
    have "(n, \<Gamma>, (Q, snd (last ((P0, sa) # xsa))) # ys) \<in> cptn_mod_nest_call"
      using a2 P_Q by blast
    then have "(\<Gamma>, (Q, snd (last ((P0, sa) # xsa))) # ys) \<in> {(f, ps). ps ! 0 = (Q, snd (((P0, sa) # xsa) ! (Suc (length xsa) - 1))) \<and> 
              (n, \<Gamma>, ps) \<in> cptn_mod_nest_call \<and> f = \<Gamma>}"
      by (simp add: cptn_eq_cptn_mod last_length)
    then show "(\<Gamma>, (P1, snd (last ((P0, sa) # xsa))) # ys) \<in> {(f, ps). ps ! 0 = (Q, snd (((P0, sa) # xsa) ! (length ((P0, sa) # xsa) - 1))) \<and> (n,\<Gamma>, ps) \<in> cptn_mod_nest_call \<and> f = \<Gamma>}"
      using P_Q by force
  qed 
  ultimately show ?thesis using a3 P_Q i using Cons_lift_catch_append by blast
qed


lemma Catch_sound4: 
assumes
  a0:"(n,\<Gamma>,x)\<in>cptn_mod_nest_call" and
  a1:"x!0 = ((Catch P Q),s)" and
  a2:"i<length x \<and> x!i=(Q,sj)" and
  a3:"\<forall>j<i. fst(x!j)\<noteq>Q" and 
  a4:"env_tran_right \<Gamma> x rely "
shows
  "\<exists>xs ys. (\<Gamma>,xs) \<in> (cpn n \<Gamma> P s) \<and> (\<Gamma>,ys) \<in> (cpn n \<Gamma> Q (snd (xs!(i-1)))) \<and> x = (map (lift_catch Q) xs)@ys"
using a0 a1 a2 a3 a4
proof (induct arbitrary: i sj P s)
  case (CptnModNestEnv \<Gamma> C st t n xsa)  
  have a1:"Catch P Q \<noteq> Q" by simp    
  then have C_catch:"C=(Catch P Q)" using CptnModNestEnv by fastforce
  then have "fst(((C, st) # (C, t) # xsa)!0) \<noteq>Q" using CptnEnv a1 by auto
  moreover have  "fst(((C, st) # (C, t) # xsa)!1) \<noteq>Q" using CptnModNestEnv a1 by auto
  moreover have "fst(((C, st) # (C, t) # xsa)!i) =Q" using CptnModNestEnv by auto
  ultimately have i_suc: "i> (Suc 0)" using CptnModNestEnv 
    by (metis Suc_eq_plus1 Suc_lessI add.left_neutral neq0_conv) 
  then obtain i' where i':"i=Suc i'" by (meson lessE) 
  then have i_minus:"i'=i-1" by auto  
  have "((C, t) # xsa) ! 0 = ((Catch P Q), t)"
    using CptnModNestEnv by auto 
  moreover have "i'< length ((C,t)#xsa) \<and> ((C,t)#xsa)!i' = (Q,sj)"
    using i' CptnModNestEnv(5) by force
  moreover have "\<forall>j<i'. fst (((C, t) # xsa) ! j) \<noteq> Q"
    using i' CptnModNestEnv(6) by force
  ultimately have hyp:"\<exists>xs ys.
     (\<Gamma>, xs) \<in> cpn n \<Gamma> P t \<and>
     (\<Gamma>, ys) \<in> cpn n \<Gamma> Q (snd (xs ! (i'-1))) \<and> (C, t) # xsa = map (lift_catch Q) xs @ ys"
    using CptnModNestEnv(3) env_tran_tail CptnModNestEnv.prems(4)  by blast 
  then obtain xs ys where xs_cp:"(\<Gamma>, xs) \<in> cpn n \<Gamma> P t \<and>
     (\<Gamma>, ys) \<in> cpn n \<Gamma> Q (snd (xs ! (i'-1))) \<and> (C, t) # xsa = map (lift_catch Q) xs @ ys"
    by fast
  have "(\<Gamma>, (P, s)#xs) \<in> cpn n \<Gamma> P s"
  proof -
    have "xs!0 = (P,t)" 
      using xs_cp unfolding cpn_def by blast
    moreover have "xs\<noteq>[]"
      using cpn_def CptnEmpty xs_cp by blast 
    ultimately obtain xs' where xs':"(n,\<Gamma>, (P,t)#xs') \<in> cptn_mod_nest_call \<and> xs=(P,t)#xs'" 
      using SmallStepCon.nth_tl xs_cp unfolding cpn_def by force
    thus ?thesis using cpn_def  
    proof -
      have "(Catch P Q, s) = (C, st)"
        using CptnModNestEnv.prems(1) by auto
      then have "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow>\<^sub>e (P, t)"
        using Catch_env_P CptnModNestEnv(1) by blast
      then show ?thesis
        by (simp add: cpn_def cptn_mod_nest_call.CptnModNestEnv xs')
    qed
  qed
  thus  ?case 
    using i_suc Cons_lift_catch_append CptnModNestEnv.prems(1) i' i_minus xs_cp
    by fastforce   
next
  case (CptnModNestSkip \<Gamma> P s t n xs)
  then show ?case
    by (metis (no_types) CptnModNestSkip.hyps(2) CptnModNestSkip.prems(1) 
    fst_conv nth_Cons_0 redex_not_Catch)
next
  case (CptnModNestThrow \<Gamma> P s t n xs)
  then show ?case  
    by (metis (no_types) CptnModNestThrow.hyps(2) CptnModNestThrow.prems(1) 
       fst_conv nth_Cons_0 redex_not_Catch)
next
  case (CptnModNestCatch1 n \<Gamma> P0 s xs zs P1)
  then show ?case
    by (metis Catch_not_c Cons_lift_catch LanguageCon.com.inject(9) 
            fst_conv map_lift_catch_all_catch nth_Cons_0)
next
  case (CptnModNestCatch2 n \<Gamma> P1 sa xsa  ys zs Q1) 
  then have P_Q:"P=P1 \<and> Q = Q1" by force
  thus ?case
  proof (cases "Q1 = Skip")
    case True thus ?thesis using catch_map_xs_ys' 
      CptnModNestCatch2 by blast
  next 
    case False note q_not_throw=this
    have "\<forall>x. x< length ((LanguageCon.com.Catch P1 Q1, sa) # zs) \<longrightarrow>
              ((LanguageCon.com.Catch P1 Q1,  sa) # zs) ! x \<noteq> (Q, sj)" using CptnModNestCatch2
    proof -
    {
      fix x
      assume x_less:"x< length ((LanguageCon.com.Catch P1 Q1,  sa) # zs)"
      have "((LanguageCon.com.Catch P1 Q1,  sa) # zs) ! x \<noteq> (Q, sj)"
      proof (cases "x < length ((LanguageCon.com.Catch P1 Q1, sa)#map (lift_catch Q1) xsa)")
        case True 
        then have eq_map:"((LanguageCon.com.Catch P1 Q1, sa) # zs) ! x = map (lift_catch Q1) ((P1, sa) # xsa) ! x"           
          by (metis (no_types) Cons_lift_catch Cons_lift_catch_append CptnModNestCatch2(6) True nth_append)
        then have  "\<exists>ci si. map (lift_catch Q1) ((P1, sa) # xsa) ! x = (Catch ci Q1,si)" 
          using True unfolding lift_catch_def
          by (metis Cons_lift_catch True eq_map map_lift_catch_all_catch surjective_pairing)
        then have  "((LanguageCon.com.Catch P1 Q1, sa) # zs) ! x \<noteq> (Q, sj)" 
          using P_Q eq_map by fastforce     
        thus ?thesis using CptnModNestCatch2(10) by auto        
      next
        case False 
        let ?s' = "snd (last ((P1, sa) # xsa))"        
      have all_throw:"\<forall>i<length ((LanguageCon.com.Skip, ?s')# ys). 
              fst (((Skip, ?s')# ys)!i) = Skip" using CptnModNestCatch2
        by (metis cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod skip_all_skip)         
      then have 
        "\<forall>x\<ge> length ((LanguageCon.com.Catch P1 Q1,  sa) # map (lift_catch Q1) xsa). 
           x<length (((LanguageCon.com.Catch P1 Q1, sa) # zs)) \<longrightarrow>
              fst (((LanguageCon.com.Catch P1 Q1, sa) # zs) ! x) = Skip"  
        using  Cons_lift_catch Cons_lift_catch_append CptnModNestCatch2.hyps(1) CptnModNestCatch2.hyps(3) 
              CptnModNestCatch2.hyps(4) CptnModNestCatch2.hyps(6) cptn_eq_cptn_mod_set 
              cptn_mod_nest_call.CptnModNestCatch2 cptn_mod_nest_cptn_mod  skip_com_all_skip 
      proof-
      {
        fix x 
        assume a1:"x\<ge> length ((Catch P1 Q1, sa) # map (lift_catch Q1) xsa)" and
               a2:"x<length (((Catch P1 Q1, sa) # zs))"
        then have "((Catch P1 Q1, sa) # zs) ! x = 
                   ((Skip, ?s')# ys) !(x - (length ((Catch P1 Q1, sa) # map (lift_catch Q1) xsa)))"
        using CptnModNestCatch2(6) by (metis Cons_lift_catch Cons_lift_catch_append not_le nth_append)
        then have"fst (((Catch P1 Q1, sa) # zs) ! x) = Skip" 
          using all_throw a1 a2 CptnModNestCatch2.hyps(6)  by auto 
      } thus ?thesis by auto
      qed       
      thus ?thesis using False  q_not_throw P_Q x_less 
        by (metis fst_conv not_le)  
    qed
    } thus ?thesis by auto
    qed
    thus ?thesis using CptnModNestCatch2(8) by fastforce    
  qed
next
  case (CptnModNestCatch3 n \<Gamma> P1 sa xsa  ys zs Q1)
  then show ?case using catch_map_xs_ys'[OF CptnModNestCatch3(1) CptnModNestCatch3(3) CptnModNestCatch3(5)
                                            CptnModNestCatch3(7) CptnModNestCatch3(8) CptnModNestCatch3(9)] 
     by blast
qed(auto) 

inductive_cases stepc_elim_cases_Catch_throw:
"\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> (Throw, Normal s1)" 

inductive_cases stepc_elim_cases_Catch_skip_c2:
"\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> (c2,s)"

inductive_cases stepc_elim_cases_Catch_skip_2:
"\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> (Skip, s)"

lemma catch_skip_throw:
 "\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> (c2,s)  \<Longrightarrow> (c2= Skip \<and> c1=Skip) \<or> (c1=Throw \<and> (\<exists>s2'. s=Normal s2'))"
apply (rule stepc_elim_cases_Catch_skip_c2)
apply fastforce
apply (auto)+
using redex_not_Catch apply auto
done

lemma catch_skip_throw1:
 "\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> (Skip,s)  \<Longrightarrow> (c1=Skip) \<or> (c1=Throw \<and> (\<exists>s2'. s=Normal s2') \<and> c2 = Skip)"
apply (rule stepc_elim_cases_Catch_skip_2)
using redex_not_Catch apply auto
using redex_not_Catch by auto


lemma Catch_sound: 
      "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p,  R, G, q,r] \<Longrightarrow>
       \<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p,  R, G, q,r] \<Longrightarrow>
       \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [r,  R, G, q,a] \<Longrightarrow>
       \<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c2 sat [r,  R, G, q,a] \<Longrightarrow>        
       Sta q R  \<Longrightarrow>  (\<forall>s. (Normal s,Normal s) \<in> G) \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (Catch c1 c2) sat [p, R, G, q,a]"
proof -  
  assume
    a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p, R, G, q,r]" and
    a1:"\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p, R, G, q,r]" and
    a2:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [r, R, G, q,a]" and    
    a3: "\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c2 sat [r, R, G, q,a]" and     
    a4: "Sta q R " and
    a5: "(\<forall>s. (Normal s, Normal s) \<in> G)"       
  { 
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"
    then have a1:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p, R, G, q,r]" 
      using a1 com_cvalidityn_def by fastforce  
    then have a3: "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c2 sat [r, R, G, q,a]"
      using a3 com_cvalidityn_def all_call by fastforce 
    have "cpn n \<Gamma> (Catch c1 c2)  s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cpn n \<Gamma> (Catch c1 c2) s" and a11:"c \<in> assum(p, R)"
      then have a10':"c \<in> cp \<Gamma> (Catch c1 c2) s"
        unfolding cpn_def cp_def
        using cptn_if_cptn_mod cptn_mod_nest_cptn_mod by blast
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have cp:"l!0=((Catch c1 c2),s) \<and> (n,\<Gamma>,l) \<in> cptn_mod_nest_call \<and> \<Gamma>=\<Gamma>1" 
        using a10 cpn_def c_prod by fastforce
      then have cp':"l!0=((Catch c1 c2),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1"
        using cptn_eq_cptn_mod_nest by auto         
      have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast
      have "c \<in> comm(G, (q,a)) F"         
      proof - 
      {
       assume l_f:"snd (last l) \<notin> Fault ` F"       
       have assum:"snd(l!0) \<in> Normal ` (p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                 (snd(l!i), snd(l!(Suc i))) \<in> R)" 
       using a11 c_prod unfolding assum_def by simp
       then have env_tran:"env_tran \<Gamma> p l R" using env_tran_def cp by blast
       then have env_tran_right: "env_tran_right \<Gamma> l R" 
         using env_tran env_tran_right_def unfolding env_tran_def by auto       
       have "(\<forall>i. Suc i<length l \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i))  \<longrightarrow>              
                 (snd(l!i), snd(l!(Suc i))) \<in> G)\<and>
             (final (last l)  \<longrightarrow>                    
                   ((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` q)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (a)))"
       proof (cases "\<forall>i<length l. fst (l!i)\<noteq> c2")
         case True 
         then have no_c2:"\<forall>i<length l. fst (l!i)\<noteq> c2" by assumption
         show ?thesis
         proof (cases "final (last l)")
           case True
           then obtain s' where "fst (last l) = Skip \<or> (fst (last l) = Throw \<and> snd (last l) = Normal s')"  
             using final_def by fast           
           thus ?thesis
           proof
             assume "fst (last l)= LanguageCon.com.Throw \<and> snd (last l) = Normal s'" 
             then have "False" using  no_c2 env_tran_right cp' cptn_eq_cptn_mod_set Catch_sound3
               by blast
             thus ?thesis by auto
           next             
             assume asm0:"fst (last l) = Skip"             
             then obtain lc1 ys where cp_lc1:"(\<Gamma>,lc1) \<in> cpn n \<Gamma> c1 s \<and> l = ((map (lift_catch c2) lc1)@((Skip,snd(last lc1))#ys))"
               using Catch_sound2 cp cptn_eq_cptn_mod_set env_tran_right no_c2 by blast
             then have cp_lc1':"(\<Gamma>,lc1) \<in> cp \<Gamma> c1 s"
               unfolding cpn_def cp_def
               using cptn_if_cptn_mod cptn_mod_nest_cptn_mod by fastforce 
             let ?m_lc1 = "map (lift_catch c2) lc1"
             let ?lm_lc1 = "(length ?m_lc1)"
             let ?last_m_lc1 = "?m_lc1!(?lm_lc1-1)"              
             have lc1_not_empty:"lc1 \<noteq> []"
               using \<Gamma>1 a10' cpn_def cp_lc1 cp by auto                 
             then have map_cp:"(\<Gamma>,?m_lc1) \<in> cpn n \<Gamma> (Catch c1 c2) s"               
             proof -
               have f1: "lc1 ! 0 = (c1, s) \<and> (n, \<Gamma>, lc1) \<in> cptn_mod_nest_call \<and> \<Gamma> = \<Gamma>"
                 using cp_lc1 unfolding cpn_def by blast
               then have f2: "(n,\<Gamma>, ?m_lc1) \<in> cptn_mod_nest_call" using lc1_not_empty
                 by (metis Cons_lift_catch SmallStepCon.nth_tl cptn_mod_nest_call.CptnModNestCatch1)
               then show ?thesis
                 using f2 f1 lc1_not_empty by (simp add: cpn_def lift_catch_def)
             qed
             then have map_cp':"(\<Gamma>,?m_lc1) \<in> cp \<Gamma> (Catch c1 c2) s" 
               unfolding cp_def cpn_def
               using cp_def cp_lc1' lift_catch_is_cptn by fastforce
             also have map_assum:"(\<Gamma>,?m_lc1) \<in> assum (p,R)"
               using sub_assum a10 a11 \<Gamma>1 cp_lc1 lc1_not_empty 
               by (metis SmallStepCon.nth_tl map_is_Nil_conv)
             ultimately have "((\<Gamma>,lc1) \<in> assum(p, R))"  
               using \<Gamma>1 assum_map_catch cp_lc1' by blast                          
             then have lc1_comm:"(\<Gamma>,lc1) \<in> comm(G, (q,r)) F"  
               using a1 cp_lc1 by (meson IntI com_validityn_def contra_subsetD)
             then have m_lc1_comm:"(\<Gamma>,?m_lc1) \<in> comm(G, (q,r)) F"
               using map_cp map_assum comm_map_catch cp_lc1' map_cp' by blast
             then have last_m_lc1:"last (?m_lc1) = (Catch (fst (last lc1)) c2,snd (last lc1))"
             proof -
               have a000:"\<forall>p c. (LanguageCon.com.Catch (fst p) c, snd p) = lift_catch c p"
                 using Cons_lift_catch by force
               then show ?thesis
                 by (simp add: last_map a000 lc1_not_empty)
             qed
             then have last_length:"last (?m_lc1) = ?last_m_lc1"  
               using lc1_not_empty last_conv_nth list.map_disc_iff by blast 
             then have l_map:"l!(?lm_lc1-1)= ?last_m_lc1" 
               using cp_lc1
               by (simp add:lc1_not_empty nth_append)
             then have lm_lc1:"l!(?lm_lc1) = (Skip, snd (last lc1))"
               using cp_lc1 by (meson nth_append_length) 
             then have step:"\<Gamma>\<turnstile>\<^sub>c(l!(?lm_lc1-1)) \<rightarrow> (l!(?lm_lc1))"
             proof -
               have "\<Gamma>\<turnstile>\<^sub>c(l!(?lm_lc1-1)) \<rightarrow>\<^sub>c\<^sub>e (l!(?lm_lc1))"
               proof -
                 have f1: "0 \<le> length ys"
                   by blast
                 moreover have  "Suc (length (map (lift_catch c2) lc1) + length ys) = 
                      length (map (lift_catch c2) lc1 @ (LanguageCon.com.Skip, snd (last lc1)) # ys)"
                   by force
                 ultimately show ?thesis
                   by (metis (no_types) Suc_diff_1 Suc_eq_plus1 cp' cp_lc1 cptn_tran_ce_i 
                              lc1_not_empty le_add_same_cancel1 length_greater_0_conv 
                    less_Suc_eq_le list.map_disc_iff)
               qed                              
               moreover have "\<not>\<Gamma>\<turnstile>\<^sub>c(l!(?lm_lc1-1)) \<rightarrow>\<^sub>e (l!(?lm_lc1))"
               using  last_m_lc1 last_length l_map
               proof -
                 have "(LanguageCon.com.Catch (fst (last lc1)) c2, snd (last lc1)) = l ! (length (map (lift_catch c2) lc1) - 1)"
                   using l_map last_m_lc1 local.last_length by presburger
                 then show ?thesis
                   by (metis LanguageCon.com.simps(30) env_c_c' lm_lc1)                   
               qed
               ultimately show ?thesis using step_ce_elim_cases by blast        
             qed
             have last_lc1_suc:"snd (l!(?lm_lc1-1)) = snd (l!?lm_lc1)"
               using l_map  last_m_lc1 lm_lc1 local.last_length by force
             then have step_catch:"\<Gamma>\<turnstile>\<^sub>c(Catch (fst (last lc1)) c2,snd (last lc1)) \<rightarrow> (Skip, snd (last lc1))"               
               using l_map last_m_lc1 lm_lc1 local.last_length local.step 
               by presburger 
             then obtain s2' where 
               last_lc1:"fst (last lc1) = Skip  \<or> 
               fst (last lc1) = Throw \<and> (snd (last lc1) = Normal s2') \<and> c2 = Skip"
             using catch_skip_throw1 by fastforce              
             then have last_lc1_skip:"fst (last lc1) = Skip" 
             proof 
                assume "fst (last lc1) = LanguageCon.com.Throw \<and>
                        snd (last lc1) = Normal s2' \<and> c2 = LanguageCon.com.Skip"
                thus ?thesis using no_c2 asm0 
                  by (simp add: cp_lc1 last_conv_nth ) 
             qed auto  
             have last_not_F:"snd (last ?m_lc1) \<notin> Fault ` F"
             proof -
               have "snd ?last_m_lc1 = snd (l!(?lm_lc1-1))"
                 using l_map by auto 
               have "(?lm_lc1-1)< length l"using cp_lc1 by fastforce
               also then have "snd (l!(?lm_lc1-1))\<notin> Fault ` F"
                 using cp' cp_lc1  l_f  last_not_F[of \<Gamma> l F]
                 by fastforce
               ultimately show ?thesis using l_map last_length by fastforce
             qed
             then have q_normal:"snd (l!?lm_lc1) \<in> Normal ` q " 
             proof -
               have last_lc1:"fst (last lc1) = Skip" 
               using last_lc1_skip by fastforce  
               have "final (last lc1)" using last_lc1 final_def 
                 by blast              
               then show ?thesis 
                 using lc1_comm last_lc1 last_not_F 
                 unfolding comm_def
                 using  last_lc1_suc comm_dest2 l_map lm_lc1 local.last_length
                 by force
             qed                                             
             then obtain s1' where normal_lm_lc1:"snd (l!?lm_lc1) = Normal s1' \<and> s1' \<in>q" 
               by auto
             have concl:"(\<forall>i ns ns'. Suc i<length l \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow>              
                 (snd(l!i), snd(l!(Suc i))) \<in> G)"
             proof-
             { fix k ns ns'
               assume a00:"Suc k<length l" and
                a21:"\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))"   
                then have i_m_l:"\<forall>i <?lm_lc1  . l!i = ?m_lc1!i" 
                  using cp_lc1
                proof -
                  have "map (lift c2) lc1 \<noteq> []"
                    by (meson lc1_not_empty list.map_disc_iff)
                  then show ?thesis
                    by (metis (no_types) cp_lc1  nth_append)
                qed                                                         
                have "(snd(l!k), snd(l!(Suc k))) \<in> G"
                proof (cases "Suc k< ?lm_lc1")
                  case True 
                  then have a11': "\<Gamma>\<turnstile>\<^sub>c(?m_lc1!k)  \<rightarrow> (?m_lc1!(Suc k))" 
                    using a11 i_m_l True
                  proof -
                    have "\<forall>n na. \<not> 0 < n - Suc na \<or> na < n "
                      using diff_Suc_eq_diff_pred zero_less_diff by presburger
                    then show ?thesis
                      by (metis (no_types) True a21 i_m_l zero_less_diff)
                  qed                 
                  then have "(snd(?m_lc1!k), snd(?m_lc1!(Suc k))) \<in> G"
                  using a11' m_lc1_comm True comm_dest1 l_f last_not_F by fastforce
                  thus ?thesis using i_m_l True by auto  
                next
                  case False 
                  then have "(Suc k=?lm_lc1) \<or> (Suc k>?lm_lc1)" by auto
                  thus ?thesis 
                  proof
                    {assume suck:"(Suc k=?lm_lc1)"
                     then have k:"k=?lm_lc1-1" by auto
                     then obtain s1' where s1'_normal:"snd(l!?lm_lc1) = Normal s1'"
                       using q_normal by fastforce
                     have G_s1':"(Normal s1', Normal s1')\<in> G" using a5 by auto
                     then show "(snd (l!k), snd (l!Suc k)) \<in> G"
                     proof -
                       have "snd (l ! k) = Normal s1'"
                         using k last_lc1_suc s1'_normal by presburger
                       then show ?thesis
                         using G_s1' s1'_normal suck by force
                     qed                                   
                    }
                  next
                  { 
                    assume a001:"Suc k>?lm_lc1"
                    have "\<forall>i. i\<ge>(length lc1) \<and> (Suc i < length l) \<longrightarrow> 
                            \<not>(\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))"
                    using lm_lc1 lc1_not_empty
                    proof -
                      have "env_tran_right \<Gamma>1 l R"
                        by (metis cp env_tran_right)
                      then show ?thesis 
                        using  cp' fst_conv length_map lm_lc1 a001 a21 a00 a4
                              normal_lm_lc1 
                        by (metis (no_types) only_one_component_tran_j)
                    qed
                    then have "\<not>(\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
                      using a00 a001 by auto                    
                    then show ?thesis using a21 by fastforce                    
                  }
                  qed 
                qed
              } thus ?thesis by auto 
             qed 
             have concr:"(final (last l)  \<longrightarrow>                    
                   ((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` q)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (a)))" 
             proof -
               have l_t:"fst (last l) = Skip" 
                 using lm_lc1 by (simp add: asm0)
               have "?lm_lc1 \<le> length l -1" using cp_lc1 by fastforce               
               also have "\<forall>i. ?lm_lc1 \<le>i \<and> i<(length l -1) \<longrightarrow>  \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))"        
                 using cp' fst_conv length_map lm_lc1 a4
                      normal_lm_lc1 only_one_component_tran_j[of \<Gamma> l ?lm_lc1 s1' q ]
                 by (metis Suc_eq_plus1 cptn_tran_ce_i env_tran_right less_diff_conv  step_ce_elim_cases)                                                                       
               ultimately have "snd (l ! (length l - 1)) \<in> Normal ` q"
                 using cp_lc1 q_normal a4 env_tran_right stability[of q R l ?lm_lc1 "(length l) -1" _ \<Gamma>] 
                 by fastforce               
               thus ?thesis using l_t 
                 by (simp add:  cp_lc1 last_conv_nth)
             qed
             note res = conjI [OF concl concr]
             then show ?thesis using  \<Gamma>1 c_prod unfolding comm_def by auto
           qed                  
         next
           case False
           then obtain lc1 where cp_lc1:"(\<Gamma>,lc1) \<in> cpn n \<Gamma> c1 s \<and> l = map (lift_catch c2) lc1" 
             using Catch_sound1 False no_c2 env_tran_right cp cptn_eq_cptn_mod_set 
             by blast 
           then have cp_lc1':"(\<Gamma>,lc1) \<in> cp \<Gamma> c1 s" 
             unfolding cpn_def cp_def
             using cptn_eq_cptn_mod_nest by fastforce
           then have "((\<Gamma>,lc1) \<in> assum(p, R))"  
              using \<Gamma>1  a10' a11 assum_map_catch cp_lc1
              by blast
           then have "(\<Gamma>, lc1)\<in> comm(G, (q,r)) F" using cp_lc1 a1
             by (meson IntI com_validityn_def contra_subsetD)
           then have "(\<Gamma>, l)\<in> comm(G, (q,r)) F"
             using comm_map_catch a10' \<Gamma>1 cp_lc1 cp_lc1' by fastforce
           then show ?thesis using l_f False
             unfolding comm_def by fastforce
         qed
       next         
         case False 
         then obtain k where k_len:"k<length l \<and> fst (l ! k) = c2"
           by blast         
         then have "\<exists>m. (m < length l \<and> fst (l ! m) = c2) \<and>
                   (\<forall>i<m. \<not> (i < length l \<and> fst (l ! i) = c2))"   
           using a0 exists_first_occ[of "(\<lambda>i. i<length l  \<and> fst (l ! i) = c2)" k] 
           by blast
         then obtain i where a0:"i<length l \<and> fst (l !i) = c2 \<and>
                                (\<forall>j<i. (fst (l ! j) \<noteq> c2))"
           by fastforce        
         then obtain s2 where li:"l!i =(c2,s2)" by (meson eq_fst_iff)
         then obtain lc1 lc2 where cp_lc1:"(\<Gamma>,lc1) \<in> (cpn n \<Gamma> c1 s) \<and> 
                                 (\<Gamma>,lc2) \<in> (cpn n \<Gamma> c2 (snd (lc1!(i-1)))) \<and> 
                                 l = (map (lift_catch c2) lc1)@lc2"
           using Catch_sound4 a0 cp env_tran_right by blast       
         then have cp_lc1':"(\<Gamma>,lc1) \<in> (cp \<Gamma> c1 s) \<and> 
                            (\<Gamma>,lc2) \<in> (cp \<Gamma> c2 (snd (lc1!(i-1))))"
           unfolding cp_def cpn_def  using cptn_eq_cptn_mod_nest by fastforce
         have i_not_fault:"snd (l!i) \<notin> Fault ` F" using a0  cp' l_f last_not_F[of \<Gamma> l F] by blast
         have length_c1_map:"length lc1 = length (map (lift_catch c2) lc1)" 
           by fastforce      
         then have i_map:"i=length lc1" 
           using cp_lc1 li a0 unfolding lift_catch_def 
         proof -
            assume a1: "(\<Gamma>, lc1) \<in> cpn n \<Gamma> c1 s \<and> (\<Gamma>, lc2) \<in> cpn n \<Gamma> c2 (snd (lc1 ! (i - 1))) \<and> l = map (\<lambda>(P, s). (Catch P c2, s)) lc1 @ lc2"
            have f2: "i < length l \<and> fst (l ! i) = c2 \<and> (\<forall>n. \<not> n < i \<or> fst (l ! n) \<noteq> c2)"
              using a0 by blast
            have f3: "(Catch (fst (lc1 ! i)) c2, snd (lc1 ! i)) = lift_catch c2 (lc1 ! i)"
              by (simp add: case_prod_unfold lift_catch_def)            
            then have "fst (l ! length lc1) = c2"
              using a1 by (simp add: cpn_def nth_append)
            thus ?thesis
              using f3 f2
              by (metis (no_types, lifting) Pair_inject a0 cp_lc1 f3 
                   length_c1_map li linorder_neqE_nat nth_append nth_map seq_and_if_not_eq(12))
         qed                  
         have lc2_l:"\<forall>j<length lc2. lc2!j=l!(i+j)"
           using cp_lc1 length_c1_map i_map a0
           by (metis nth_append_length_plus)                                                             
         have lc1_not_empty:"lc1 \<noteq> []"
           using cp cp_lc1 unfolding cpn_def by fastforce      
         have lc2_not_empty:"lc2 \<noteq> []"
           using cpn_def cp_lc1 a0 i_map by force              
         have l_is:"s2= snd (last lc1)"
         using cp_lc1 li a0 lc1_not_empty unfolding cpn_def
         by (auto simp add: i_map last_conv_nth lc2_l)
         let ?m_lc1 = "map (lift_catch c2) lc1"
         (* let ?lm_lc1 = "(length ?m_lc1)"
         let ?last_m_lc1 = "?m_lc1!(?lm_lc1-1)" *)                         
         have last_m_lc1:"l!(i-1) = (Catch (fst (last lc1)) c2,s2)"
           using i_map  cp_lc1 l_is last_lift_catch last_snd_catch lc1_not_empty length_c1_map           
         by (metis (no_types, lifting) One_nat_def diff_Suc_less last_conv_nth length_greater_0_conv nth_append prod.collapse)
         have last_mcl1_not_F:"snd (last ?m_lc1) \<notin> Fault ` F"
           by (metis One_nat_def i_not_fault l_is last_conv_nth last_snd_catch li list.map_disc_iff snd_conv)                                  
         have map_cp:"(\<Gamma>,?m_lc1) \<in> cpn n \<Gamma> (Catch c1 c2) s"               
         proof -
           have f1: "lc1 ! 0 = (c1, s) \<and> (n,\<Gamma>, lc1) \<in> cptn_mod_nest_call \<and> \<Gamma> = \<Gamma>"
             using cp_lc1 cpn_def by blast
           then have f2: "(n, \<Gamma>, ?m_lc1) \<in> cptn_mod_nest_call" using lc1_not_empty
             by (metis Cons_lift_catch SmallStepCon.nth_tl cptn_mod_nest_call.CptnModNestCatch1)                           
           then show ?thesis
             using f2 f1 lc1_not_empty by (simp add: cpn_def lift_catch_def)
         qed
         then have map_cp':"(\<Gamma>,?m_lc1) \<in> cp \<Gamma> (Catch c1 c2) s"
           unfolding cp_def cpn_def using cptn_eq_cptn_mod_nest by fastforce
         also have map_assum:"(\<Gamma>,?m_lc1) \<in> assum (p,R)"
           using sub_assum a10 a11 \<Gamma>1 cp_lc1 lc1_not_empty 
           by (metis SmallStepCon.nth_tl map_is_Nil_conv)
         ultimately have "((\<Gamma>,lc1) \<in> assum(p, R))"  
           using \<Gamma>1 assum_map_catch using assum_map cp_lc1 cp_lc1' by blast                          
         then have lc1_comm:"(\<Gamma>,lc1) \<in> comm(G, (q,r)) F"  
           using a1 cp_lc1 by (meson IntI com_validityn_def contra_subsetD)
         then have m_lc1_comm:"(\<Gamma>,?m_lc1) \<in> comm(G, (q,r)) F"
           using map_cp' map_assum comm_map_catch cp_lc1 cp_lc1'  by blast         
         then have "\<Gamma>\<turnstile>\<^sub>c(l!(i-1)) \<rightarrow> (l!i)"
         proof -
           have "\<Gamma>\<turnstile>\<^sub>c(l!(i-1)) \<rightarrow>\<^sub>c\<^sub>e (l!(i))"
             by (metis Suc_eq_plus1 Suc_pred' a0 cp' cptn_tran_ce_i i_map 
                  lc1_not_empty length_greater_0_conv)
           moreover have "\<not>\<Gamma>\<turnstile>\<^sub>c(l!(i-1)) \<rightarrow>\<^sub>e (l!i)"           
             using li last_m_lc1
             by (metis (no_types, lifting) env_c_c' seq_and_if_not_eq(12))
           ultimately show ?thesis using step_ce_elim_cases by blast
         qed         
         then have step:"\<Gamma>\<turnstile>\<^sub>c(Catch (fst (last lc1)) c2,s2) \<rightarrow> (c2, s2)"
           using last_m_lc1  li by fastforce
         then obtain s2' where 
           last_lc1:"(fst (last lc1) = Skip \<and> c2 = Skip) \<or> 
            fst (last lc1) = Throw \<and> (s2 = Normal s2')" 
           using catch_skip_throw by blast    
         have final:"final (last lc1)" 
           using last_lc1 l_is unfolding final_def by auto
         have normal_last:"fst (last lc1) = Skip \<and> snd (last lc1) \<in> Normal ` q \<or>
                        fst (last lc1) = Throw \<and> snd (last lc1) \<in> Normal ` r"
         proof -         
           have "snd (last lc1) \<notin> Fault ` F"
             using i_not_fault l_is li by auto
           then show ?thesis
             using final comm_dest2 lc1_comm by blast
         qed
         obtain s2' where lastlc1_normal:"snd (last lc1) = Normal s2'" 
           using normal_last by blast
         then have Normals2:"s2 = Normal s2'" by (simp add: l_is) 
         have Gs2':" (Normal s2', Normal s2')\<in>G" using a5 by auto              
         have concl:
           "(\<forall>i. Suc i<length l \<longrightarrow> 
           \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow>                              
             (snd(l!i), snd(l!(Suc i))) \<in> G)"
         proof-
         { fix k ns ns'
           assume a00:"Suc k<length l" and
            a21:"\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))"   
            have i_m_l:"\<forall>j <i . l!j = ?m_lc1!j"             
            proof -
              have "map (lift c2) lc1 \<noteq> []"
                by (meson lc1_not_empty list.map_disc_iff)
              then show ?thesis 
                using cp_lc1 i_map length_c1_map by (fastforce simp:nth_append)              
            qed 
            have "(snd(l!k), snd(l!(Suc k))) \<in> G"
            proof (cases "Suc k< i")
              case True 
              then have a11': "\<Gamma>\<turnstile>\<^sub>c(?m_lc1!k)  \<rightarrow> (?m_lc1!(Suc k))" 
                using a11 i_m_l True
              proof -
                have "\<forall>n na. \<not> 0 < n - Suc na \<or> na < n "
                  using diff_Suc_eq_diff_pred zero_less_diff by presburger
                then show ?thesis using True a21 i_m_l by force                  
              qed                                                             
              have "Suc k < length ?m_lc1" using True i_map length_c1_map by metis
              then have "(snd(?m_lc1!k), snd(?m_lc1!(Suc k))) \<in> G"
              using a11' last_mcl1_not_F m_lc1_comm True i_map length_c1_map comm_dest1[of \<Gamma>] 
                by blast
              thus ?thesis using i_m_l True by auto  
            next
              case False                                            
              have "(Suc k=i) \<or> (Suc k>i)" using False by auto
              thus ?thesis 
              proof
              { assume suck:"(Suc k=i)" 
                then have k:"k=i-1" by auto                                                            
                then show "(snd (l!k), snd (l!Suc k)) \<in> G"
                  using Gs2' Normals2 last_m_lc1 li suck by auto               
              }
              next
              { 
                assume a001:"Suc k>i"
                then have k:"k\<ge>i" by fastforce
                then obtain k' where k':"k=i+k'" 
                  using add.commute le_Suc_ex by blast
                {assume skip:"c2=Skip"
                 then have "\<forall>k. k\<ge>i \<and> (Suc k < length l) \<longrightarrow> 
                            \<not>(\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
                  using Normals2 li lastlc1_normal a21 a001 a00 a4
                        a0 skip env_tran_right cp'
                  by (metis SmallStepCon.final_def SmallStepCon.no_step_final' Suc_lessD skip_com_all_skip)                                      
                 then have ?thesis using a21 a001 k a00 by blast
                }  note left=this
                {assume "c2\<noteq>Skip"
                 then have "fst (last lc1) = Throw"
                   using last_m_lc1 last_lc1 by simp                                     
                 then have s2_normal:"s2 \<in> Normal ` r" 
                   using normal_last lastlc1_normal Normals2
                   by fastforce
                 have length_lc2:"length l=i+length lc2" 
                       using i_map cp_lc1 by fastforce
                 have "(\<Gamma>,lc2) \<in>  assum (r,R)" 
                 proof -
                   have left:"snd (lc2!0) \<in> Normal ` r" 
                     using li lc2_l s2_normal lc2_not_empty by fastforce 
                   {
                     fix j
                     assume j_len:"Suc j<length lc2" and
                            j_step:"\<Gamma>\<turnstile>\<^sub>c(lc2!j)  \<rightarrow>\<^sub>e (lc2!(Suc j))"                     
                     then have suc_len:"Suc (i + j)<length l" using j_len length_lc2
                       by fastforce
                     also then have "\<Gamma>\<turnstile>\<^sub>c(l!(i+j))  \<rightarrow>\<^sub>e (l! (Suc (i+ j)))"
                        using lc2_l j_step j_len by fastforce
                     ultimately have "(snd(lc2!j), snd(lc2!(Suc j))) \<in> R"
                        using assum suc_len lc2_l j_len cp by fastforce 
                   }
                   then show ?thesis using left 
                     unfolding assum_def by fastforce
                 qed
                 also have "(\<Gamma>,lc2) \<in> cpn n \<Gamma> c2 s2"
                   using cp_lc1 i_map l_is last_conv_nth lc1_not_empty by fastforce                 
                 ultimately have comm_lc2:"(\<Gamma>,lc2) \<in>  comm (G, (q,a)) F"
                   using a3 unfolding com_validityn_def by auto
                 have lc2_last_f:"snd (last lc2)\<notin> Fault ` F" 
                   using lc2_l lc2_not_empty l_f cp_lc1 by fastforce
                 have suck':"Suc k' < length lc2" 
                   using k' a00 length_lc2 by arith
                 moreover then have "\<Gamma>\<turnstile>\<^sub>c(lc2!k')  \<rightarrow> (lc2!(Suc k'))"  
                   using k' lc2_l a21 by fastforce                 
                 ultimately have "(snd (lc2! k'), snd (lc2 ! Suc k')) \<in> G"
                   using comm_lc2  lc2_last_f comm_dest1[of \<Gamma> lc2 G q a F k'] 
                   by blast
                 then have ?thesis using suck' lc2_l k' by fastforce
                }                    
                then show ?thesis using left by auto                 
              }
              qed 
            qed
          } thus ?thesis by auto 
         qed note left=this
         have right:"(final (last l)  \<longrightarrow>                    
                   ((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` q)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (a)))"
         proof -
         { assume final_l:"final (last l)" 
           have eq_last_lc2_l:"last l=last lc2" by (simp add: cp_lc1 lc2_not_empty)
           then have final_lc2:"final (last lc2)" using final_l by auto
           {
             assume lst_lc1_skip:"fst (last lc1) = Skip"                        
             then have c2_skip:"c2 = Skip" 
               using  step lastlc1_normal LanguageCon.com.distinct(17) last_lc1 
               by auto                            
             have Skip:"fst (l!(length l - 1)) = Skip"
             using li Normals2  env_tran_right cp' c2_skip a0
                     i_skip_all_skip[of \<Gamma> l i "(length l) - 1" _] 
                by fastforce                       
             have s2_a:"s2 \<in> Normal ` q"
               using normal_last 
               by (simp add: lst_lc1_skip l_is)
             then have "\<forall>ia. i \<le> ia \<and> ia < length l - 1 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c l ! ia \<rightarrow>\<^sub>e l ! Suc ia"
               using c2_skip li Normals2 a0 cp' env_tran_right  final_def
               by (metis (no_types, hide_lams) One_nat_def SmallStepCon.no_step_final' 
                   Suc_lessD add.right_neutral add_Suc_right 
                   cptn_tran_ce_i i_skip_all_skip less_diff_conv step_ce_elim_cases)                           
             then have "snd (l!(length l - 1)) \<in> Normal ` q \<and> fst (l!(length l - 1)) = Skip"               
               using a0 s2_a li a4 env_tran_right stability[of q R l i "(length l) -1" _ \<Gamma>] Skip                
               by (metis One_nat_def Suc_pred length_greater_0_conv lessI linorder_not_less list.size(3) 
                   not_less0 not_less_eq_eq snd_conv)
             then have "((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` q)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (a))" 
              using a0 by (metis last_conv_nth list.size(3) not_less0)                           
          }  note left = this
          {  assume "fst (last lc1) = Throw"                 
             then have s2_normal:"s2 \<in> Normal ` r" 
               using normal_last lastlc1_normal Normals2
               by fastforce
             have length_lc2:"length l=i+length lc2" 
                   using i_map cp_lc1 by fastforce
             have "(\<Gamma>,lc2) \<in>  assum (r,R)" 
             proof -
               have left:"snd (lc2!0) \<in> Normal ` r" 
                 using li lc2_l s2_normal lc2_not_empty by fastforce 
               {
                 fix j
                 assume j_len:"Suc j<length lc2" and
                        j_step:"\<Gamma>\<turnstile>\<^sub>c(lc2!j)  \<rightarrow>\<^sub>e (lc2!(Suc j))"
                 
                 then have suc_len:"Suc (i + j)<length l" using j_len length_lc2
                   by fastforce
                 also then have "\<Gamma>\<turnstile>\<^sub>c(l!(i+j))  \<rightarrow>\<^sub>e (l! (Suc (i+ j)))"
                    using lc2_l j_step j_len by fastforce
                 ultimately have "(snd(lc2!j), snd(lc2!(Suc j))) \<in> R"
                    using assum suc_len lc2_l j_len cp by fastforce 
               }
               then show ?thesis using left 
                 unfolding assum_def by fastforce
             qed
             also have "(\<Gamma>,lc2) \<in> cpn n \<Gamma> c2 s2"
               using cp_lc1 i_map l_is last_conv_nth lc1_not_empty by fastforce
             ultimately have comm_lc2:"(\<Gamma>,lc2) \<in>  comm (G, (q,a)) F"
               using a3 unfolding com_validityn_def by auto
             have lc2_last_f:"snd (last lc2)\<notin> Fault ` F" 
               using lc2_l lc2_not_empty l_f cp_lc1 by fastforce             
             then have "((fst (last lc2) = Skip \<and> 
                    snd (last lc2) \<in> Normal ` q)) \<or>
                    (fst (last lc2) = Throw \<and> 
                    snd (last lc2) \<in> Normal ` (a))" 
             using final_lc2 comm_lc2 unfolding comm_def by auto
             then have "((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` q)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (a))" 
             using eq_last_lc2_l by auto
          }
          then have "((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` q)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (a))" 
            using left using last_lc1 by auto
        } thus ?thesis by auto qed         
     thus ?thesis using left l_f \<Gamma>1 unfolding comm_def by force       
       qed             
     } thus ?thesis using \<Gamma>1 unfolding comm_def by auto qed
   } thus ?thesis by auto qed 
 } thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed



lemma DynCom_sound: 
      "(\<forall>s \<in> p. ((\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (c1 s) sat [p, R, G, q,a]) \<and> 
                 (\<forall>n. (\<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (c1 s) sat [p,R, G, q,a])))) \<Longrightarrow>
        (\<forall>s. (Normal s, Normal s) \<in> G) \<Longrightarrow>
       (Sta p R) \<and> (Sta q R) \<and> (Sta a R) \<Longrightarrow>        
        \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (DynCom c1) sat [p,  R, G, q,a]"
proof -  
  assume
    a0:"(\<forall>s \<in> p. ((\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (c1 s) sat [p, R, G, q,a]) \<and> 
                 (\<forall>n. (\<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (c1 s) sat [p, R, G, q,a]))))" and    
    a1:"\<forall>s. (Normal s, Normal s) \<in> G" and  
    a2: "(Sta p R) \<and> (Sta q R) \<and> (Sta a R)"               
  { 
    fix s
    assume all_DynCom:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"     
    then have a0:"(\<forall>s \<in> p. (\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (c1 s) sat [p, R, G, q,a]))"
      using a0 unfolding com_cvalidityn_def by fastforce     
    have "cpn n \<Gamma>(DynCom c1) s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cpn n \<Gamma> (DynCom c1) s" and a11:"c \<in> assum(p, R)"
      then have a10':"c \<in> cp \<Gamma> (DynCom c1) s"
        unfolding cp_def cpn_def
        using cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod by fastforce
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof - 
      {assume l_f:"snd (last l) \<notin> Fault ` F"       
        have cp:"l!0=(DynCom c1,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" 
          using a10' cp_def c_prod by fastforce
        have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast
        have assum:"snd(l!0) \<in> Normal ` (p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                   (snd(l!i), snd(l!(Suc i))) \<in> R)" 
       using a11 c_prod unfolding assum_def by simp
       then have env_tran:"env_tran \<Gamma> p l R" using env_tran_def cp by blast
       then have env_tran_right: "env_tran_right \<Gamma> l R" 
         using env_tran env_tran_right_def unfolding env_tran_def by auto
       obtain ns where s_normal:"s=Normal ns \<and> ns\<in> p" 
         using cp assum by fastforce       
       have concl:"(\<forall>i. Suc i<length l \<longrightarrow> 
               \<Gamma>1\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow>             
                 (snd(l!i), snd(l!(Suc i))) \<in> G)"
       proof -
       { fix k ns ns'
         assume a00:"Suc k<length l" and
                a21:"\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))"                                     
         obtain j where before_k_all_evnt:"j\<le>k \<and>  (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<and> (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
           using a00 a21 exist_first_comp_tran cp by blast
         then obtain cj sj csj ssj where pair_j:"(\<Gamma>\<turnstile>\<^sub>c(cj,sj)  \<rightarrow> (csj,ssj)) \<and> cj = fst (l!j) \<and> sj = snd (l!j) \<and> csj = fst (l!(Suc j)) \<and> ssj = snd(l!(Suc j))"
           by fastforce                                             
         have k_basic:"cj = (DynCom c1) \<and> sj \<in> Normal ` (p)" 
           using  pair_j before_k_all_evnt a2 cp env_tran_right  assum a00 stability[of p R l 0 j j \<Gamma>]
           by force
         then obtain s' where ss:"sj = Normal s' \<and> s'\<in> (p)" by auto 
         then have ssj_normal_s:"ssj = Normal s'" 
           using before_k_all_evnt k_basic pair_j a0 
           by (metis snd_conv stepc_Normal_elim_cases(10))                     
         have "(snd(l!k), snd(l!(Suc k))) \<in> G"
           using ss a2 unfolding Satis_def
         proof (cases "k=j")   
           case True                                  
           have "(Normal s', Normal s')\<in>G" using a1 by fastforce
           thus "(snd (l ! k), snd (l ! Suc k)) \<in>  G"
             using pair_j k_basic True ss ssj_normal_s by auto
         next
           case False   
           have j_k:"j<k" using  before_k_all_evnt False by fastforce                      
           thus "(snd (l ! k), snd (l ! Suc k)) \<in> G"
           proof -
             have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce
             have p1:"s'\<in>p \<and> ssj=Normal s'" using ss ssj_normal_s by fastforce
             then have c1_valid:"(\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (c1 s') sat [p, R, G, q,a])"
               using a0 by fastforce
             have cj:"csj= (c1 s')" using k_basic pair_j ss a0 s_normal
             proof -
               have "\<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.DynCom c1, Normal s') \<rightarrow> (csj, ssj)"
                 using k_basic pair_j ss by force
               then have "(csj, ssj) = (c1 s', Normal s')"
                 by (meson stepc_Normal_elim_cases(10))
               then show ?thesis
                 by blast
             qed                                                       
             moreover then have "cpn n \<Gamma> csj ssj \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
               using a2 com_validityn_def cj p1 c1_valid by blast             
             moreover then have "l!(Suc j) = (csj, Normal s')" 
               using before_k_all_evnt pair_j cj ssj_normal_s
               by fastforce
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
               using  p1 j_length  a11 \<Gamma>1  ssj_normal_s                     
               using a10 cpn_assum_induct by fastforce                                        
             then show ?thesis 
             using a00 a21  a10' \<Gamma>1  j_k j_length l_f
             cptn_comm_induct[of \<Gamma> l "DynCom c1" s _ "Suc j" G q a F k ]
             unfolding Satis_def by fastforce                         
          qed            
       qed 
       } thus ?thesis by (simp add: c_prod cp) qed
       have concr:"(final (last l)  \<longrightarrow>                   
                   ((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` q)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (a)))"
       proof-
       { 
         assume valid:"final (last l)"                       
         have "\<exists>k. k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))) \<and> final (l!(Suc k))"
         proof -             
           have len_l:"length l > 0" using cp using cptn.simps by blast 
           then obtain a1 l1 where l:"l=a1#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
           have last_l:"last l = l!(length l-1)"
            using last_length [of a1 l1] l by fastforce         
           have final_0:"\<not>final(l!0)" using cp unfolding final_def by auto
           have "0\<le> (length l-1)" using len_l last_l by auto
           moreover have "(length l-1) < length l" using len_l by auto
           moreover have "final (l!(length l-1))" using valid last_l by auto
           moreover have "fst (l!0) = DynCom c1" using cp by auto
           ultimately show ?thesis 
             using a2 cp final_exist_component_tran_final env_tran_right final_0 
             by blast 
          qed
          then obtain k where a21: "k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))) \<and> final (l!(Suc k))"
            by auto
          then have a00:"Suc k<length l" by fastforce
          then obtain j where before_k_all_evnt:"j\<le>k \<and>  (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<and> (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
            using a00 a21 exist_first_comp_tran cp by blast
          then obtain cj sj csj ssj where pair_j:"(\<Gamma>\<turnstile>\<^sub>c(cj,sj)  \<rightarrow> (csj,ssj)) \<and> cj = fst (l!j) \<and> sj = snd (l!j) \<and> csj = fst (l!(Suc j)) \<and> ssj = snd(l!(Suc j))"
            by fastforce         
          have "((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` q)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (a))"
          proof -
            have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce                                 
            then have k_basic:"cj = (DynCom c1) \<and> sj \<in> Normal ` (p)" 
              using a2 pair_j before_k_all_evnt cp env_tran_right assum stability[of p R l 0 j j \<Gamma>]
              by force
            then obtain s' where ss:"sj = Normal s' \<and> s'\<in> (p)" by auto 
            then have ssj_normal_s:"ssj = Normal s'" 
              using before_k_all_evnt k_basic pair_j a0 
              by (metis snd_conv stepc_Normal_elim_cases(10))
            have cj:"csj=c1 s'" using k_basic pair_j ss a0
              by (metis fst_conv stepc_Normal_elim_cases(10))                
            moreover have p1:"s'\<in>p" using ss by blast 
            moreover then have "cpn n \<Gamma> csj ssj \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
              using a0 com_validityn_def cj by blast
            moreover then have "l!(Suc j) = (csj, Normal s')" 
              using before_k_all_evnt pair_j cj ssj_normal_s
              by fastforce
            ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
              using  j_length a10 a11 \<Gamma>1  ssj_normal_s              
              by (meson contra_subsetD cpn_assum_induct)               
            thus ?thesis       
              using j_length l_f drop_comm a10' \<Gamma>1 cptn_comm_induct[of \<Gamma> l "DynCom c1" s _ "Suc j" G q a F "Suc j"] valid  
              by blast
           qed
         } thus ?thesis by auto 
         qed
       note res = conjI [OF concl concr]}               
       thus ?thesis using  c_prod unfolding comm_def by force qed      
    } thus ?thesis by auto qed 
  } thus ?thesis by (auto simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed

lemma Guard_sound:
  "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> g, R, G, q,a] \<Longrightarrow>
   (\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> g, R, G, q,a]) \<Longrightarrow>   
   Sta (p \<inter> g) R \<Longrightarrow> (\<forall>s. (Normal s, Normal s) \<in> G) \<Longrightarrow>
    \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (Guard f g c1) sat [p \<inter> g, R, G, q,a]"
proof -  
  assume
    a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [(p \<inter> g) , R, G, q,a]" and
    a1:"(\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> g, R, G, q,a])" and        
    a2: "Sta (p \<inter> g) R" and
    a3: "\<forall>s. (Normal s, Normal s) \<in> G"
  { 
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"  
    then have a1:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> g, R, G, q,a]" 
      using a1 com_cvalidityn_def by fastforce
    have "cpn n \<Gamma> (Guard f g c1)  s \<inter> assum(p \<inter> g, R) \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cpn n \<Gamma> (Guard f g c1) s" and a11:"c \<in> assum(p \<inter> g, R)"
      then have a10':"c \<in> cp \<Gamma> (Guard f g c1) s" 
        unfolding cpn_def cp_def using cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod by fastforce
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof - 
      {assume l_f:"snd (last l) \<notin> Fault ` F"       
        have cp:"l!0=((Guard f g c1),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10' cp_def c_prod by fastforce
        have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast
        have assum:"snd(l!0) \<in> Normal ` (p \<inter> g) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                   (snd(l!i), snd(l!(Suc i))) \<in> R)" 
       using a11 c_prod unfolding assum_def by simp
       then have env_tran:"env_tran \<Gamma> (p \<inter> g) l R" using env_tran_def cp by blast
       then have env_tran_right: "env_tran_right \<Gamma> l R" 
         using env_tran env_tran_right_def unfolding env_tran_def by auto
       have concl:"(\<forall>i. Suc i<length l \<longrightarrow> 
               \<Gamma>1\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow>                                            
                 (snd(l!i), snd(l!(Suc i))) \<in> G)"
       proof -
       { fix k ns ns'
         assume a00:"Suc k<length l" and
                a21:"\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))"                                                        
         obtain j where before_k_all_evnt:"j\<le>k \<and>  (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<and> (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
           using a00 a21 exist_first_comp_tran cp by blast
         then obtain cj sj csj ssj where pair_j:"(\<Gamma>\<turnstile>\<^sub>c(cj,sj)  \<rightarrow> (csj,ssj)) \<and> cj = fst (l!j) \<and> sj = snd (l!j) \<and> csj = fst (l!(Suc j)) \<and> ssj = snd(l!(Suc j))"
           by fastforce                                             
         have k_basic:"cj =(Guard f g c1) \<and> sj \<in> Normal ` (p \<inter> g)" 
           using  pair_j before_k_all_evnt cp env_tran_right a2 assum a00 stability[of "p \<inter> g" R l 0 j j \<Gamma>]
           by force
         then obtain s' where ss:"sj = Normal s' \<and> s'\<in> (p \<inter> g)" by auto 
         then have ssj_normal_s:"ssj = Normal s'" 
           using before_k_all_evnt k_basic pair_j a0 stepc_Normal_elim_cases(2)
           by (metis (no_types, lifting)  IntD2 prod.inject)                                
         have "(snd(l!k), snd(l!(Suc k))) \<in> G"
           using ss a2 unfolding Satis_def
         proof (cases "k=j")   
           case True                                  
           have " (Normal s', Normal s')\<in>G" using a3 by auto 
           thus "(snd (l ! k), snd (l ! Suc k)) \<in>  G"
             using pair_j k_basic True ss ssj_normal_s by auto
         next
           case False   
           have j_k:"j<k" using  before_k_all_evnt False by fastforce                      
           thus "(snd (l ! k), snd (l ! Suc k)) \<in>  G"
           proof -
             have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce
             have cj:"csj=c1" using k_basic pair_j ss a0
               by (metis (no_types, lifting) IntD2 fst_conv stepc_Normal_elim_cases(2))                             
             moreover have p1:"s' \<in> (p \<inter> g)" using ss by blast 
             moreover then have "cpn n \<Gamma> csj ssj \<inter> assum(p \<inter> g, R) \<subseteq> comm(G, (q,a)) F"
               using a1 com_validityn_def cj by blast
             moreover then have "l!(Suc j) = (csj, Normal s')" 
               using before_k_all_evnt pair_j cj ssj_normal_s
               by fastforce
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
               using  j_length a10 a11 \<Gamma>1  ssj_normal_s
                     cpn_assum_induct
               by fastforce                         
             then show ?thesis 
             using a00 a21  a10' \<Gamma>1  j_k j_length l_f
             cptn_comm_induct[of \<Gamma> l "(Guard f g c1)" s _ "Suc j" G q a F k ]
             unfolding Satis_def by fastforce                         
          qed            
       qed 
       } thus ?thesis by (simp add: c_prod cp) qed
       have concr:"(final (last l)  \<longrightarrow>                   
                   ((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` q)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (a)))"
       proof-
       { 
         assume valid:"final (last l)"                       
         have "\<exists>k. k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))) \<and> final (l!(Suc k))"
         proof -             
           have len_l:"length l > 0" using cp using cptn.simps by blast 
           then obtain a1 l1 where l:"l=a1#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
           have last_l:"last l = l!(length l-1)"
            using last_length [of a1 l1] l by fastforce         
           have final_0:"\<not>final(l!0)" using cp unfolding final_def by auto
           have "0\<le> (length l-1)" using len_l last_l by auto
           moreover have "(length l-1) < length l" using len_l by auto
           moreover have "final (l!(length l-1))" using valid last_l by auto
           moreover have "fst (l!0) = (Guard f g c1)" using cp by auto
           ultimately show ?thesis 
             using  cp final_exist_component_tran_final env_tran_right final_0 
             by blast 
          qed
          then obtain k where a21: "k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))) \<and> final (l!(Suc k))"
            by auto
          then have a00:"Suc k<length l" by fastforce
          then obtain j where before_k_all_evnt:"j\<le>k \<and>  (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<and> (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
            using a00 a21 exist_first_comp_tran cp by blast
          then obtain cj sj csj ssj where pair_j:"(\<Gamma>\<turnstile>\<^sub>c(cj,sj)  \<rightarrow> (csj,ssj)) \<and> cj = fst (l!j) \<and> sj = snd (l!j) \<and> csj = fst (l!(Suc j)) \<and> ssj = snd(l!(Suc j))"
            by fastforce         
          have "((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` q)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (a))"
          proof -
            have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce                                 
            then have k_basic:"cj = (Guard f g c1) \<and> sj \<in> Normal ` (p \<inter> g)" 
              using  pair_j before_k_all_evnt cp env_tran_right a2 assum a00 stability[of "p \<inter> g" R l 0 j j \<Gamma>]
              by force
            then obtain s' where ss:"sj = Normal s' \<and> s'\<in> (p \<inter> g)" by auto 
            then have ssj_normal_s:"ssj = Normal s'" 
              using before_k_all_evnt k_basic pair_j a1
              by (metis (no_types, lifting) IntD2 Pair_inject stepc_Normal_elim_cases(2))               
            have cj:"csj=c1" using k_basic pair_j ss a0
              by (metis (no_types, lifting) fst_conv IntD2 stepc_Normal_elim_cases(2))                              
            moreover have p1:"s' \<in> (p \<inter> g)" using ss by blast 
            moreover then have "cpn n \<Gamma> csj ssj \<inter> assum((p \<inter> g), R) \<subseteq> comm(G, (q,a)) F"
              using a1 com_validityn_def cj by blast
            moreover then have "l!(Suc j) = (csj, Normal s')" 
              using before_k_all_evnt pair_j cj ssj_normal_s
              by fastforce
            ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
              using  j_length a10 a11 \<Gamma>1  ssj_normal_s cpn_assum_induct
              by fastforce    
            thus ?thesis       
              using j_length l_f drop_comm a10' \<Gamma>1 cptn_comm_induct[of \<Gamma> l "(Guard f g c1)" s _ "Suc j" G q a F "Suc j"] valid  
              by blast
           qed
         } thus ?thesis by auto 
         qed
       note res = conjI [OF concl concr]}               
       thus ?thesis using  c_prod unfolding comm_def by force qed      
    } thus ?thesis by auto qed 
  } thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed


lemma Guarantee_sound:
  "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [(p \<inter> g),  R, G, q,a] \<Longrightarrow>
   \<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> g, R, G, q,a] \<Longrightarrow>  
   Sta p R \<Longrightarrow> 
   f\<in>F \<Longrightarrow>
   (\<forall>s. (Normal s, Normal s) \<in> G) \<Longrightarrow> 
   \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (Guard f g c1) sat [p, R, G, q,a]"
proof -  
  assume
    a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> g, R, G, q,a]" and
    a1:"\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> g, R, G, q,a]" and      
    a2: "Sta p R" and
    a3: "(\<forall>s. (Normal s, Normal s) \<in> G)" and
    a4: "f\<in>F"    
  { 
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"  
    then have a1:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> g, R, G, q,a]" 
      using a1 com_cvalidityn_def by fastforce
    have "cpn n \<Gamma> (Guard f g c1)  s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cpn n \<Gamma> (Guard f g c1) s" and a11:"c \<in> assum(p, R)"
      then have a10':"c \<in> cp \<Gamma> (Guard f g c1) s"
        unfolding cp_def cpn_def using cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod by fast
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof - 
      {assume l_f:"snd (last l) \<notin> Fault ` F"       
        have cp:"l!0=((Guard f g c1),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10' cp_def c_prod by fastforce
        have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast
        have assum:"snd(l!0) \<in> Normal ` (p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                   (snd(l!i), snd(l!(Suc i))) \<in> R)" 
       using a11 c_prod unfolding assum_def by simp
       then have env_tran:"env_tran \<Gamma> p l R" using env_tran_def cp by blast
       then have env_tran_right: "env_tran_right \<Gamma> l R" 
         using env_tran env_tran_right_def unfolding env_tran_def by auto                     
       have concl:"(\<forall>i ns ns'. Suc i<length l \<longrightarrow> 
               \<Gamma>1\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow>                 
                 (snd(l!i), snd(l!(Suc i))) \<in> G)"
       proof -
       { fix k ns ns'
         assume a00:"Suc k<length l" and
                a21:"\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))"                                         
         obtain j where before_k_all_evnt:"j\<le>k \<and>  (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<and> (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
           using a00 a21 exist_first_comp_tran cp by blast
         then obtain cj sj csj ssj where pair_j:"(\<Gamma>\<turnstile>\<^sub>c(cj,sj)  \<rightarrow> (csj,ssj)) \<and> cj = fst (l!j) \<and> sj = snd (l!j) \<and> csj = fst (l!(Suc j)) \<and> ssj = snd(l!(Suc j))"
           by fastforce                                                               
         have k_basic:"cj =(Guard f g c1) \<and> sj \<in> Normal ` (p)" 
           using  pair_j before_k_all_evnt cp env_tran_right a2 assum a00 stability[of p R l 0 j j \<Gamma>]
           by force
         then obtain s' where ss:"sj = Normal s' \<and> s'\<in> (p)" by auto          
         have or:"s'\<in> (g \<union> (-g))" by fastforce
         {assume "s' \<in> g"
          then have k_basic:"cj =(Guard f g c1) \<and> sj \<in> Normal ` (p \<inter> g)" 
            using ss k_basic by fastforce
          then have ss: "sj = Normal s' \<and> s'\<in>  (p \<inter> g)"
            using ss by fastforce
          have ssj_normal_s:"ssj = Normal s'" 
           using ss before_k_all_evnt k_basic pair_j a0 stepc_Normal_elim_cases(2)
           by (metis (no_types, lifting) IntD2 prod.inject)                                
          have "(snd(l!k), snd(l!(Suc k))) \<in> G"
           using ss a2 unfolding Satis_def
         proof (cases "k=j")   
           case True                                  
           have "(Normal s', Normal s') \<in> G" using a3 by auto
           thus "(snd (l ! k), snd (l ! Suc k)) \<in>  G"
             using pair_j k_basic True ss ssj_normal_s by auto
         next
           case False   
           have j_k:"j<k" using  before_k_all_evnt False by fastforce                      
           thus "(snd (l ! k), snd (l ! Suc k)) \<in>  G"
           proof -
             have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce
             have cj:"csj=c1" using k_basic pair_j ss a0
               by (metis (no_types, lifting) fst_conv IntD2 stepc_Normal_elim_cases(2))                             
             moreover have p1:"s' \<in> (p \<inter> g)" using ss by blast 
             moreover then have "cpn n \<Gamma> csj ssj \<inter> assum((p \<inter> g), R) \<subseteq> comm(G, (q,a)) F"
               using a1 com_validityn_def cj by blast
             moreover then have "l!(Suc j) = (csj, Normal s')" 
               using before_k_all_evnt pair_j cj ssj_normal_s
               by fastforce
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
               using  j_length a10 a11 \<Gamma>1  ssj_normal_s cpn_assum_induct
               by fastforce                     
              then show ?thesis 
              using a3 a00 a21  a10' \<Gamma>1  j_k j_length l_f
               cptn_comm_induct[of \<Gamma> l "(Guard f g c1)" s _ "Suc j" G q a F k]
              unfolding Satis_def by fastforce                         
            qed            
          qed
         } note p1=this
         {(* assume "s' \<in> (Collect (not (set_fun g)))"
          then have "s'\<notin>g" by fastforce *)
          assume "s'\<notin>g"
          then have csj_skip:"csj= Skip \<and> ssj=Fault f" using k_basic ss pair_j 
            by (meson Pair_inject stepc_Normal_elim_cases(2))
          then have "snd (last l) = Fault f" using pair_j
          proof -
            have "j = k" 
            proof -
              have f1: "k < length l"
                using a00 by linarith
              have "\<not> SmallStepCon.final (l ! k)"
                by (metis SmallStepCon.no_step_final' a21)
              then have "\<not> Suc j \<le> k"
                using f1 SmallStepCon.final_def cp csj_skip i_skip_all_skip pair_j by blast
              then show ?thesis
                by (metis Suc_leI before_k_all_evnt le_eq_less_or_eq)
            qed
            then have False
              using pair_j csj_skip by (metis a00 a4 cp image_eqI l_f last_not_F)
            then show ?thesis
              by metis
          qed
          then have False using a4 l_f by auto          
         }
         then have "(snd(l!k), snd(l!(Suc k))) \<in> G"
           using p1 or by fastforce
       } thus ?thesis by (simp add: c_prod cp) qed
       have concr:"(final (last l)  \<longrightarrow>                   
                   ((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` q)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (a)))"
       proof-
       { 
         assume valid:"final (last l)"                       
         have "\<exists>k. k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))) \<and> final (l!(Suc k))"
         proof -             
           have len_l:"length l > 0" using cp using cptn.simps by blast 
           then obtain a1 l1 where l:"l=a1#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
           have last_l:"last l = l!(length l-1)"
            using last_length [of a1 l1] l by fastforce         
           have final_0:"\<not>final(l!0)" using cp unfolding final_def by auto
           have "0\<le> (length l-1)" using len_l last_l by auto
           moreover have "(length l-1) < length l" using len_l by auto
           moreover have "final (l!(length l-1))" using valid last_l by auto
           moreover have "fst (l!0) = (Guard f g c1)" using cp by auto
           ultimately show ?thesis 
             using  cp final_exist_component_tran_final env_tran_right final_0 
             by blast 
          qed
          then obtain k where a21: "k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))) \<and> final (l!(Suc k))"
            by auto
          then have a00:"Suc k<length l" by fastforce
          then obtain j where before_k_all_evnt:"j\<le>k \<and>  (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<and> (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
            using a00 a21 exist_first_comp_tran cp by blast
          then obtain cj sj csj ssj where pair_j:"(\<Gamma>\<turnstile>\<^sub>c(cj,sj)  \<rightarrow> (csj,ssj)) \<and> cj = fst (l!j) \<and> sj = snd (l!j) \<and> csj = fst (l!(Suc j)) \<and> ssj = snd(l!(Suc j))"
            by fastforce         
          have "((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` q)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (a))"
          proof -
            have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce                                 
            have k_basic:"cj =(Guard f g c1) \<and> sj \<in> Normal ` (p)" 
             using  pair_j before_k_all_evnt cp env_tran_right a2 assum a00 stability[of p R l 0 j j \<Gamma>]
             by force
            then obtain s' where ss:"sj = Normal s' \<and> s'\<in> (p)" by auto 
            have or:"s'\<in> (g \<union> (-g))" by fastforce
            {assume "s' \<in> g"
             then have k_basic:"cj =(Guard f g c1) \<and> sj \<in> Normal ` (p \<inter> g)" 
               using ss k_basic by fastforce
             then have ss: "sj = Normal s' \<and> s'\<in> (p \<inter> g)"
               using ss by fastforce
             then have ssj_normal_s:"ssj = Normal s'" 
              using before_k_all_evnt k_basic pair_j a1
              by (metis (no_types, lifting) Pair_inject IntD2 stepc_Normal_elim_cases(2))               
             have cj:"csj=c1" using k_basic pair_j ss a0
              by (metis (no_types, lifting) fst_conv IntD2 stepc_Normal_elim_cases(2))                              
             moreover have p1:"s'\<in>(p \<inter> g)" using ss by blast 
             moreover then have "cpn n \<Gamma> csj ssj \<inter> assum((p \<inter> g), R)  \<subseteq> comm(G, (q,a)) F"
               using a1 com_validityn_def cj by blast
             moreover then have "l!(Suc j) = (csj, Normal s')" 
               using before_k_all_evnt pair_j cj ssj_normal_s
               by fastforce
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
               using  j_length a10 a11 \<Gamma>1  ssj_normal_s cpn_assum_induct
               by fastforce                 
            then have ?thesis       
              using j_length l_f drop_comm a10' \<Gamma>1 
                     cptn_comm_induct[of \<Gamma> l "(Guard f g c1)" s _ "Suc j" G q a F "Suc j"] valid  
              by blast
           }note left=this        
           {
            (* assume "s' \<in> (Collect (not (set_fun g)))"
            then have "s'\<notin>g" by fastforce *)
             assume "s'\<notin>g"
          then have "csj= Skip \<and> ssj=Fault f" using k_basic ss pair_j 
            by (meson Pair_inject stepc_Normal_elim_cases(2))
          then have "snd (last l) = Fault f" using pair_j
            by (metis a4 cp imageI j_length l_f last_not_F)            
          then have False using a4 l_f by auto           
           }
           thus ?thesis using or left by auto qed
         } thus ?thesis by auto 
         qed
       note res = conjI [OF concl concr]}               
       thus ?thesis using  c_prod unfolding comm_def by force qed      
    } thus ?thesis by auto qed 
  } thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed

lemma WhileNone:   
   "\<Gamma>\<turnstile>\<^sub>c (While b c1, s1) \<rightarrow> (LanguageCon.com.Skip, t1) \<Longrightarrow>   
    (n,\<Gamma>, (Skip, t1) # xsa) \<in> cptn_mod_nest_call \<Longrightarrow>  
    \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> b,R, G, p,a] \<Longrightarrow>
    Sta p R \<Longrightarrow>
    Sta (p \<inter> (-b)) R \<Longrightarrow>
    Sta a R \<Longrightarrow>
    (\<forall>s. (Normal s, Normal s) \<in> G) \<Longrightarrow>            
    (\<Gamma>, (While b c1, s1) # (LanguageCon.com.Skip, t1) # xsa) \<in> assum (p, R) \<Longrightarrow>    
    (\<Gamma>, (While b c1, s1) # (LanguageCon.com.Skip, t1) # xsa) \<in> comm (G,(p \<inter> (-b)),a) F"
proof -
  assume a0:"\<Gamma>\<turnstile>\<^sub>c (While b c1, s1) \<rightarrow> (LanguageCon.com.Skip, t1)" and
         a1:"(n,\<Gamma>, (Skip, t1) # xsa) \<in> cptn_mod_nest_call" and
         a2:" \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> b,R, G, p,a]" and
         a3:"Sta p R" and
         a4:"Sta (p \<inter> (-b)) R" and
         a5:"Sta a R" and
         a6:"\<forall>s. (Normal s, Normal s) \<in> G" and
         a7:"(\<Gamma>, (While b c1, s1) # (LanguageCon.com.Skip, t1) # xsa) \<in> assum (p, R)"         
  obtain s1' where s1N:"s1=Normal s1' \<and> s1'\<in>p" using a7 unfolding assum_def by fastforce
  then have s1_t1:"s1'\<notin> b \<and> t1=s1" using a0
    using LanguageCon.com.distinct(5) prod.inject 
    by (fastforce elim:stepc_Normal_elim_cases(7))
  then have t1_Normal_post:"t1\<in> Normal ` (p \<inter> (-b))"
    using s1N by fastforce
  also have "(\<Gamma>, (While b c1, s1) # (LanguageCon.com.Skip, t1) # xsa)\<in>cptn"
    using a1 a0 cptn.simps
    using cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod by fastforce
  ultimately have assum_skip:
    "(\<Gamma>,(LanguageCon.com.Skip, t1) # xsa) \<in> assum (( p \<inter> (-b)), R)"
    using a1 a7 tl_of_assum_in_assum1 t1_Normal_post by fastforce
  have skip_comm:"(\<Gamma>,(LanguageCon.com.Skip, t1) # xsa) \<in> 
               comm (G,(( p \<inter> (-b)),a)) F" 
  proof- 
    obtain \<Theta> where  "(\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p , R, G, q,a])" by auto
    moreover have "\<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> Skip sat [( p \<inter> (-b)), R, G, ( p \<inter> (-b)),a]"
      using Skip_sound[of "(p \<inter> - b)"]  a4 a6   by blast
    ultimately show ?thesis
      using assum_skip  a1  unfolding com_cvalidityn_def com_validityn_def cpn_def
      by fastforce
  qed    
  have G_ref:"(Normal s1', Normal s1')\<in>G" using a6 by fastforce
  thus ?thesis using skip_comm ctran_in_comm[of s1'] s1N s1_t1 by blast
qed 

lemma while1:
   "(n,\<Gamma>, ((c, Normal s1) # xs1)) \<in> cptn_mod_nest_call \<Longrightarrow>    
    s1 \<in> b \<Longrightarrow>
    xsa = map (lift (While b c)) xs1 \<Longrightarrow>
    \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [p \<inter> b,R, G, p,a] \<Longrightarrow>    
    (\<Gamma>, (While b c, Normal s1) #
        (Seq c (LanguageCon.com.While b c), Normal s1) # xsa)
       \<in> assum (p, R)  \<Longrightarrow>               
    \<forall>s. (Normal s, Normal s) \<in> G \<Longrightarrow> 
     (\<Gamma>, (LanguageCon.com.While b c, Normal s1) #
         (LanguageCon.com.Seq c (LanguageCon.com.While b c), Normal s1) # xsa)
    \<in> comm (G, p\<inter>(-b), a) F"
proof -
assume   
  a0:"(n,\<Gamma>, ((c, Normal s1) # xs1)) \<in> cptn_mod_nest_call" and
  a1:"s1 \<in> b" and
  a2:"xsa = map (lift (While b c)) xs1" and
  a3:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [p \<inter> b,R, G, p,a]" and
  a4:"(\<Gamma>, (While b c, Normal s1) #
        (Seq c (While b c), Normal s1) # xsa)
       \<in> assum (p, R) " and  
  a5:"\<forall>s. (Normal s,Normal s) \<in> G" 
  have seq_map:"(Seq c (While b c), Normal s1) # xsa=
           map (lift (While b c)) ((c,Normal s1)#xs1)"
  using a2 unfolding lift_def by fastforce
  have step:"\<Gamma>\<turnstile>\<^sub>c(While b c,Normal s1) \<rightarrow> (Seq c (While b c),Normal s1)" using a1
    WhileTruec by fastforce
  have s1_normal:"s1 \<in> p \<and> s1 \<in> b " using a4 a1 unfolding assum_def by fastforce
  then have G_ref:"(Normal s1, Normal s1) \<in> G"  using a5 by fastforce 
  have s1_collect_p: "Normal s1\<in> Normal ` (p \<inter> b)" using s1_normal by fastforce
  have "(\<Gamma>, map (lift (While b c)) ((c,Normal s1)#xs1))\<in>cptn" 
    using a2 cptn_eq_cptn_mod_nest lift_is_cptn a0  by blast 
  then have cptn_seq:"(\<Gamma>,(Seq c (While b c), Normal s1) # xsa) \<in>cptn" 
    using seq_map by auto
  then have "(\<Gamma>, (While b c, Normal s1) # (Seq c (While b c), Normal s1) # xsa) \<in> cptn"
    using step by (simp add: cptn.CptnComp) 
  then have assum_seq:"(\<Gamma>,(Seq c (While b c), Normal s1) # xsa)\<in>assum (p, R)"
    using a4 tl_of_assum_in_assum1 s1_collect_p by fastforce
  have cp_c:"(\<Gamma>, ((c, Normal s1) # xs1)) \<in> (cpn n \<Gamma> c (Normal s1))"
    using a0 unfolding cpn_def by fastforce
  then have cp_c':"(\<Gamma>, ((c, Normal s1) # xs1)) \<in> (cp \<Gamma> c (Normal s1))"
    unfolding cp_def cpn_def using cptn_eq_cptn_mod_nest by fastforce    
  also have cp_seq:"(\<Gamma>, (Seq c (While b c), Normal s1) # xsa) \<in> (cp \<Gamma> (Seq c (While b c)) (Normal s1))"
    using cptn_seq unfolding cp_def by fastforce
  ultimately have "(\<Gamma>, ((c, Normal s1) # xs1)) \<in> assum(p,R)"  
    using assum_map assum_seq seq_map by fastforce  
  then have "(\<Gamma>, ((c, Normal s1) # xs1)) \<in> assum((p \<inter> b),R)"
    unfolding assum_def using s1_collect_p by fastforce
  then have "(\<Gamma>, ((c, Normal s1) # xs1)) \<in> comm(G,(p,a)) F"
    using a3 cp_c unfolding com_validityn_def by fastforce
  then have "(\<Gamma>, (Seq c (While b c), Normal s1) # xsa) \<in> comm(G,(p,a)) F"
    using cp_seq cp_c' comm_map seq_map by fastforce
  then have "(\<Gamma>, (While b c, Normal s1) # (Seq c (While b c), Normal s1) # xsa) \<in> comm(G,(p,a)) F"
    using G_ref ctran_in_comm by fastforce
  also have "\<not> final (last ((While b c, Normal s1) # (Seq c (While b c), Normal s1) # xsa))"
    using seq_map unfolding final_def lift_def  by (simp add: case_prod_beta' last_map)  
  ultimately show ?thesis using not_final_in_comm[of \<Gamma>] by blast
qed

lemma while2:
   " (n,\<Gamma>, (While b c, Normal s1) #
         (Seq c (While b c), Normal s1) # xsa) \<in>cptn_mod_nest_call \<Longrightarrow>
    (n, \<Gamma>, (c, Normal s1) # xs1) \<in> cptn_mod_nest_call \<Longrightarrow>
    fst (last ((c, Normal s1) # xs1)) = LanguageCon.com.Skip \<Longrightarrow>
    s1 \<in> b \<Longrightarrow>
    xsa = map (lift (While b c)) xs1 @
    (While b c, snd (last ((c, Normal s1) # xs1))) # ys \<Longrightarrow>
    (n, \<Gamma>, (While b c, snd (last ((c, Normal s1) # xs1))) # ys)
      \<in> cptn_mod_nest_call \<Longrightarrow>
     (\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [p \<inter> b, R, G, p,a] \<Longrightarrow>    
       (\<Gamma>, (While b c, snd (last ((c, Normal s1) # xs1))) # ys)
         \<in> assum (p, R) \<Longrightarrow>
       (\<Gamma>, (While b c, snd (last ((c, Normal s1) # xs1))) # ys)
          \<in> comm (G, p \<inter> (-b), a) F) \<Longrightarrow>
    \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [ p \<inter> b, R, G, p,a] \<Longrightarrow>
    (\<Gamma>, (While b c, Normal s1) #
      (Seq c (While b c), Normal s1) # xsa)
      \<in> assum (p, R)  \<Longrightarrow>
     \<forall>s. (Normal s,Normal s) \<in> G  \<Longrightarrow>     
    (\<Gamma>, (While b c, Normal s1) #
         (Seq c (While b c), Normal s1) # xsa)
      \<in> comm (G,( p \<inter> (-b), a)) F"
proof -
assume a00:"(n, \<Gamma>, (While b c, Normal s1) #
         (Seq c (While b c), Normal s1) # xsa) \<in>cptn_mod_nest_call" and
       a0:"(n,\<Gamma>, (c, Normal s1) # xs1) \<in> cptn_mod_nest_call" and
       a1:" fst (last ((c, Normal s1) # xs1)) = LanguageCon.com.Skip" and
       a2:"s1 \<in> b" and
       a3:"xsa = map (lift (While b c)) xs1 @
            (While b c, snd (last ((c, Normal s1) # xs1))) # ys" and
       a4:"(n,\<Gamma>, (While b c, snd (last ((c, Normal s1) # xs1))) # ys)
            \<in> cptn_mod_nest_call" and
       a5:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [p \<inter> b, R, G, p,a]" and       
       a6:"(\<Gamma>, (While b c, Normal s1) #
               (Seq c (While b c), Normal s1) # xsa)
             \<in> assum (p, R)" and
       a7:"(\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [p \<inter> b, R, G, p,a] \<Longrightarrow>    
           (\<Gamma>, (While b c, snd (last ((c, Normal s1) # xs1))) # ys)
             \<in> assum (p, R) \<Longrightarrow>
           (\<Gamma>, (While b c, snd (last ((c, Normal s1) # xs1))) # ys)
             \<in> comm (G,p \<inter> (-b), a) F)" and
       a8:"\<forall>s. (Normal s, Normal s) \<in> G" 
  let ?l= "(While b c, Normal s1) #
           (Seq c (While b c), Normal s1) # xsa"
  let ?sub_l="((While b c, Normal s1) # 
                 (Seq c (While b c), Normal s1) # 
                 map (lift (While b c)) xs1)"
  {
  assume final_not_fault:"snd (last ?l) \<notin> Fault ` F"
  have a0':"(\<Gamma>, (c, Normal s1) # xs1) \<in> cptn"
    using cptn_eq_cptn_mod_nest using a0 by auto
  have a4:"(\<Gamma>, (While b c, snd (last ((c, Normal s1) # xs1))) # ys) \<in> cptn" 
    using cptn_eq_cptn_mod_nest using a4 by blast
  have seq_map:"(Seq c (While b c), Normal s1) # map (lift (While b c)) xs1=
           map (lift (While b c)) ((c,Normal s1)#xs1)"
  using a2 unfolding lift_def by fastforce
  have step:"\<Gamma>\<turnstile>\<^sub>c(While b c,Normal s1) \<rightarrow> (Seq c (While b c),Normal s1)" using a2
    WhileTruec by fastforce
  have s1_normal:"s1\<in>p \<and> s1 \<in> b " using a6 a2 unfolding assum_def by fastforce
  have G_ref:"(Normal s1, Normal s1)\<in>G " 
    using a8 by blast
  have s1_collect_p: "Normal s1\<in> Normal ` (p \<inter> b)" using s1_normal by fastforce
  have "(\<Gamma>, map (lift (While b c)) ((c,Normal s1)#xs1))\<in>cptn" 
    using a2 cptn_eq_cptn_mod lift_is_cptn a0' by fastforce
  then have cptn_seq:"(\<Gamma>,(Seq c (While b c), Normal s1) # map (lift (While b c)) xs1) \<in>cptn" 
    using seq_map by auto
  then have "(\<Gamma>, (While b c, Normal s1) # 
                 (Seq c (While b c), Normal s1) # 
                  map (lift (While b c)) xs1) \<in> cptn"
    using step by (simp add: cptn.CptnComp) 
  also have "(\<Gamma>, (While b c, Normal s1) #
                 (Seq c (While b c), Normal s1) #
                  map (lift (While b c)) xs1)
          \<in> assum (p, R)"
    using a6 a3 sub_assum by force 
  ultimately have assum_seq:"(\<Gamma>,(Seq c (While b c), Normal s1)  # 
                       map (lift (While b c)) xs1) \<in> assum (p, R)"
    using a6 tl_of_assum_in_assum1 s1_collect_p 
          tl_of_assum_in_assum   by fastforce
  have cpn_c:"(\<Gamma>, ((c, Normal s1) # xs1)) \<in> (cpn n \<Gamma> c (Normal s1))"
    using a0 unfolding cpn_def by fastforce
  have cp_c:"(\<Gamma>, ((c, Normal s1) # xs1)) \<in> (cp \<Gamma> c (Normal s1))"
    using a0' unfolding cp_def by fastforce  
  also have cp_seq:"(\<Gamma>, (Seq c (While b c), Normal s1) # map (lift (While b c)) xs1) \<in> (cp \<Gamma> (Seq c (While b c)) (Normal s1))"
    using cptn_seq unfolding cp_def by fastforce
  ultimately have "(\<Gamma>, ((c, Normal s1) # xs1)) \<in> assum(p,R) "  
    using assum_map assum_seq seq_map  by fastforce  
  then have "(\<Gamma>, ((c, Normal s1) # xs1)) \<in> assum((p \<inter> b),R) "
    unfolding assum_def using s1_collect_p by fastforce
  then have c_comm:"(\<Gamma>, ((c, Normal s1) # xs1)) \<in> comm(G,(p,a)) F"
    using a5 cpn_c unfolding com_validityn_def by fastforce
  then have "(\<Gamma>, (Seq c (While b c), Normal s1) # map (lift (While b c)) xs1) \<in> comm(G,(p,a)) F"
    using cp_seq cp_c comm_map seq_map by fastforce
  then have comm_while:"(\<Gamma>, (While b c, Normal s1) # 
                            (Seq c (While b c), Normal s1) # 
                            map (lift (While b c)) xs1) \<in> comm(G,(p,a)) F"
    using G_ref ctran_in_comm by fastforce
  have final_last_c:"final (last ((c,Normal s1)#xs1))"
    using a1 a3 unfolding final_def by fastforce
  have last_while1:"snd (last (map (lift (While b c)) ((c,Normal s1)#xs1))) = snd (last ((c, Normal s1) # xs1))"
    unfolding lift_def by (simp add: case_prod_beta' last_map)
  have last_while2:"(last (map (lift (While b c)) ((c,Normal s1)#xs1))) =
           last ((While b c, Normal s1) # (Seq c (While b c), Normal s1) # map (lift (While b c)) xs1)"
    using seq_map by fastforce
  have not_fault_final_last_c:
    "snd (last ( (c,Normal s1)#xs1)) \<notin> Fault ` F"
  proof -    
    have "(length ?sub_l) - 1 < length ?l" 
      using a3 by fastforce
    then have "snd (?l!((length ?sub_l) - 1))\<notin> Fault ` F"
      using final_not_fault a3 a00 last_not_F[of \<Gamma> ?l F]
           cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod by blast  
    thus ?thesis using last_while2 last_while1 seq_map
      by (metis (no_types) Cons_lift_append  a3 diff_Suc_1 last_length length_Cons lessI nth_Cons_Suc nth_append)
  qed
  then have last_c_normal:"snd (last ( (c,Normal s1)#xs1)) \<in> Normal ` (p)"
    using c_comm a1 unfolding comm_def final_def by fastforce    
  then obtain sl where sl:"snd (last ( (c,Normal s1)#xs1)) = Normal sl" by fastforce
  have while_comm:"(\<Gamma>, (While b c, snd (last ((c, Normal s1) # xs1))) # ys) \<in> comm(G,(p\<inter>(-b),a)) F"
  proof -
    have assum_while: "(\<Gamma>, (While b c, snd (last ((c, Normal s1) # xs1))) # ys)
             \<in> assum (p, R)"
      using last_c_normal a3 a6 sub_assum_r[of \<Gamma> ?sub_l "(While b c, snd (last ((c, Normal s1) # xs1)))"  ys p R p] 
      by fastforce
    thus ?thesis using a5 a7 by fastforce
  qed      
  have "sl\<in>p" using last_c_normal sl by fastforce
  then have G1_ref:"(Normal sl, Normal sl)\<in>G" using a8 by auto
  also have "snd (last ?sub_l) = Normal sl"
    using last_while1 last_while2 sl by fastforce
  ultimately have ?thesis 
    using  cptn_eq_cptn_mod_nest a00 a3 sl while_comm comm_union[OF comm_while]  
    by fastforce    
  } note p1 =this
  {
    assume final_not_fault:"\<not> (snd (last ?l) \<notin> Fault ` F)"
    then have ?thesis unfolding comm_def by fastforce
  } thus ?thesis using p1 by fastforce
qed

lemma while3:
   "(n, \<Gamma>, (c, Normal s1) # xs1) \<in> cptn_mod_nest_call \<Longrightarrow>    
    fst (last ((c, Normal s1) # xs1)) = Throw \<Longrightarrow>
    s1 \<in> b \<Longrightarrow>
    snd (last ((c, Normal s1) # xs1)) = Normal sl \<Longrightarrow>
    (n,\<Gamma>, (Throw, Normal sl) # ys) \<in> cptn_mod_nest_call   \<Longrightarrow>
    \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [p \<inter> b,R, G, p,a] \<Longrightarrow>    
    (\<Gamma>, (While b c, Normal s1) #
         (Seq c (While b c), Normal s1) #  
         (map (lift (While b c)) xs1 @
           (Throw, Normal sl) # ys))
       \<in> assum (p, R)  \<Longrightarrow>        
     Sta p R \<Longrightarrow>
     Sta a R \<Longrightarrow> \<forall>s. (Normal s, Normal s) \<in> G \<Longrightarrow> 
    (\<Gamma>, (While b c, Normal s1) #
         (Seq c (While b c), Normal s1) #          
         ((map (lift (While b c)) xs1 @
           (Throw, Normal sl) # ys))) \<in> comm (G, p\<inter> (-b), a) F
"
proof -
assume a0:"(n,\<Gamma>, (c, Normal s1) # xs1) \<in> cptn_mod_nest_call" and
       a1:"fst (last ((c, Normal s1) # xs1)) = Throw" and
       a2:"s1 \<in> b" and
       a3:"snd (last ((c, Normal s1) # xs1)) = Normal sl" and
       a4:"(n,\<Gamma>, (Throw, Normal sl) # ys) \<in> cptn_mod_nest_call" and
       a5:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [p \<inter> b, R, G, p,a]" and
       a6:"(\<Gamma>, (While b c, Normal s1) #
           (Seq c (While b c), Normal s1) #  
           (map (lift (While b c)) xs1 @
             (Throw, Normal sl) # ys))
           \<in> assum (p, R)" and      
       a7: "Sta p R" and
       a8: "Sta a R" and       
       a10:"\<forall>s. (Normal s,Normal s) \<in> G"  
  have seq_map:"(Seq c (While b c), Normal s1) # map (lift (While b c)) xs1=
           map (lift (While b c)) ((c,Normal s1)#xs1)"
  using a2 unfolding lift_def by fastforce
  have step:"\<Gamma>\<turnstile>\<^sub>c(While b c,Normal s1) \<rightarrow> (Seq c (While b c),Normal s1)" using a2
    WhileTruec by fastforce
  have s1_normal:"s1\<in>p \<and> s1 \<in> b " using a6 a2 unfolding assum_def by fastforce
  then have G_ref:"(Normal s1, Normal s1)\<in>G" using a10 by auto
  have s1_collect_p: "Normal s1\<in> Normal ` (p \<inter> b)" using s1_normal by fastforce
  have "(n, \<Gamma>, map (lift (While b c)) ((c,Normal s1)#xs1))\<in>cptn_mod_nest_call" 
    using a2  lift_is_cptn a0
    by (metis cptn_mod_nest_call.CptnModNestSeq1 seq_map) 
  then have cptn_seq:"(n,\<Gamma>,(Seq c (While b c), Normal s1) # map (lift (While b c)) xs1) \<in>cptn_mod_nest_call" 
    using seq_map by auto
  then have cptn:"(n,\<Gamma>, (While b c, Normal s1) # 
                 (Seq c (While b c), Normal s1) # 
                  map (lift (While b c)) xs1) \<in> cptn_mod_nest_call"
     by (meson a0 a2 cptn_mod_nest_call.CptnModNestWhile1) 
  also have "(\<Gamma>, (LanguageCon.com.While b c, Normal s1) #
         (LanguageCon.com.Seq c (LanguageCon.com.While b c), Normal s1) #
         map (lift (LanguageCon.com.While b c)) xs1)
          \<in> assum (p, R) "
    using a6 sub_assum by force 
  ultimately have assum_seq:"(\<Gamma>,(Seq c (While b c), Normal s1)  # 
                       map (lift (While b c)) xs1) \<in> assum (p, R)"
    using a6 tl_of_assum_in_assum1 s1_collect_p 
          tl_of_assum_in_assum cptn_eq_cptn_mod_nest  by fast
  have cpn_c:"(\<Gamma>, ((c, Normal s1) # xs1)) \<in> (cpn n \<Gamma> c (Normal s1))"
    using a0 unfolding cpn_def by fastforce
  then have cp_c:"(\<Gamma>, ((c, Normal s1) # xs1)) \<in> (cp \<Gamma> c (Normal s1))"
    unfolding cp_def cpn_def using cptn_eq_cptn_mod_nest by auto
  moreover have cp_seq:"(\<Gamma>, (Seq c (While b c), Normal s1) # map (lift (While b c)) xs1) \<in> (cpn n \<Gamma> (Seq c (While b c)) (Normal s1))"
    using cptn_seq unfolding cpn_def by fastforce
  then have cp_seq':"(\<Gamma>, (Seq c (While b c), Normal s1) # map (lift (While b c)) xs1) \<in> (cp \<Gamma> (Seq c (While b c)) (Normal s1))"
    unfolding cp_def cpn_def using cptn_eq_cptn_mod_nest by auto
  ultimately have "(\<Gamma>, ((c, Normal s1) # xs1)) \<in> assum(p,R)"  
    using assum_map assum_seq seq_map  by fastforce
  then have "(\<Gamma>, ((c, Normal s1) # xs1)) \<in> assum((p \<inter> b),R)"
    unfolding assum_def using s1_collect_p by fastforce
  then have c_comm:"(\<Gamma>, ((c, Normal s1) # xs1)) \<in> comm(G,(p,a)) F"
    using a5 cpn_c unfolding com_validityn_def by fastforce
  then have "(\<Gamma>, (Seq c (While b c), Normal s1) # map (lift (While b c)) xs1) \<in> comm(G,(p,a)) F"
    using cp_seq' cp_c comm_map seq_map by fastforce
  then have comm_while:"(\<Gamma>, (While b c, Normal s1) # (Seq c (While b c), Normal s1) # map (lift (While b c)) xs1) \<in> comm(G,(p,a)) F"
    using G_ref ctran_in_comm by fastforce
  have final_last_c:"final (last ((c,Normal s1)#xs1))"
    using a1 a3 unfolding final_def by fastforce
  have not_fault_final_last_c:
    "snd (last ( (c,Normal s1)#xs1)) \<notin> Fault ` F"
    using a3 by fastforce
  then have sl_a:"Normal sl \<in> Normal ` (a)"  
    using final_last_c a1 c_comm unfolding comm_def
    using  a3 comm_dest2   
    by auto
  have last_while1:"snd (last (map (lift (While b c)) ((c,Normal s1)#xs1))) = snd (last ((c, Normal s1) # xs1))"
    unfolding lift_def by (simp add: case_prod_beta' last_map)
  have last_while2:"(last (map (lift (While b c)) ((c,Normal s1)#xs1))) =
           last ((While b c, Normal s1) # (Seq c (While b c), Normal s1) # map (lift (While b c)) xs1)"
    using seq_map by fastforce
  have throw_comm:"(\<Gamma>, (Throw, Normal sl) # ys) \<in> comm(G,(p\<inter>(-b),a)) F"
  proof -
    have assum_throw: "(\<Gamma>, (Throw, Normal sl) # ys) \<in> assum (a,R)"
      using sl_a a6 sub_assum_r[of _ "(LanguageCon.com.While b c, Normal s1) #
         (LanguageCon.com.Seq c (LanguageCon.com.While b c), Normal s1) #
         map (lift (LanguageCon.com.While b c)) xs1" "(Throw, Normal sl)" ] 
      by fastforce
    also have "(\<Gamma>,(Throw, Normal sl) # ys) \<in> cpn n \<Gamma> Throw (Normal sl)" 
      unfolding cpn_def using a4 by fastforce
    ultimately show ?thesis using Throw_sound[of a R G \<Gamma>] a10 a8   
      unfolding com_cvalidityn_def com_validityn_def by fast
  qed  
  have p1:"(LanguageCon.com.While b c, Normal s1) #
    (LanguageCon.com.Seq c (LanguageCon.com.While b c), Normal s1) #
    map (lift (LanguageCon.com.While b c)) xs1 \<noteq>
    [] \<and>
    (LanguageCon.com.Throw, Normal sl) # ys \<noteq> []" by auto  
  have "sl \<in> a" using sl_a by fastforce
  then have G1_ref:"(Normal sl, Normal sl) \<in> G" using a10 by auto
  moreover have "snd (last ((While b c, Normal s1) # 
                  (Seq c (While b c), Normal s1) # 
                  map (lift (While b c)) xs1)) = Normal sl"
    using last_while1 last_while2 a3 by fastforce
  moreover have "snd (((LanguageCon.com.Throw, Normal sl) # ys) ! 0) = Normal sl"
    by (metis nth_Cons_0 snd_conv)
  ultimately have G:"(snd (last ((While b c, Normal s1) # 
                  (Seq c (While b c), Normal s1) # 
                  map (lift (While b c)) xs1)),
                  snd (((LanguageCon.com.Throw, Normal sl) # ys) ! 0)) \<in> G" by auto
  have cptn:"(\<Gamma>, ((LanguageCon.com.While b c, Normal s1) #
          (LanguageCon.com.Seq c (LanguageCon.com.While b c), Normal s1) #
          map (lift (LanguageCon.com.While b c)) xs1) @
         (LanguageCon.com.Throw, Normal sl) # ys)
    \<in> cptn" using cptn a4  a0 a1 a3 a4 cptn_eq_cptn_mod_set cptn_mod.CptnModWhile3 s1_normal 
             cptn_eq_cptn_mod_nest by (metis append_Cons)
  show ?thesis using a0  comm_union[OF comm_while throw_comm p1 G cptn] by auto       
qed


inductive_cases stepc_elim_cases_while_throw [cases set]:
 "\<Gamma>\<turnstile>\<^sub>c(While b c, s) \<rightarrow> (Throw, t)"


lemma WhileSound_aux:
 "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> b, R, G, p,a] \<Longrightarrow>
  Sta p R \<Longrightarrow>
  Sta  (p \<inter> (-b)) R \<Longrightarrow> 
  Sta a R \<Longrightarrow>    
  (n, \<Gamma>,x)\<in> cptn_mod_nest_call \<Longrightarrow> 
  \<forall>s. (Normal s, Normal s) \<in> G \<Longrightarrow>
  \<forall>s xs. x = ((While b c1),s)#xs \<longrightarrow> 
     (\<Gamma>,x)\<in>assum(p,R) \<longrightarrow> 
     (\<Gamma>,x) \<in> comm (G,(( p \<inter> (-b)),a)) F"
proof -
  assume a0: "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> b, R, G, p,a] " and
         a1: "Sta p R" and
         a2: "Sta  (p \<inter> (-b)) R" and
         a3: "Sta a R" and
         a4: "(n,\<Gamma>,x)\<in> cptn_mod_nest_call" and
         a5: "\<forall>s. (Normal s, Normal s) \<in> G" 
   {fix xs s 
   assume while_xs:"x=((While b c1),s)#xs" and
          x_assum:"(\<Gamma>,x)\<in>assum(p,R)"
   have "(\<Gamma>,x) \<in> comm (G,(( p \<inter> (-b)),a)) F"
   using a4 a0  while_xs x_assum
   proof (induct arbitrary: xs s c1 rule:cptn_mod_nest_call.induct)
     case (CptnModNestOne  \<Gamma> C s1) thus ?case 
       using CptnModOne unfolding comm_def final_def
       by auto
   next
     case (CptnModNestEnv  \<Gamma> C s1 t1 n xsa) 
     then have c_while:"C = While b c1" by fastforce
     have "(\<Gamma>, (C, t1) # xsa) \<in> assum (p, R) \<longrightarrow>
                (\<Gamma>, (C, t1) # xsa) \<in> comm (G, p \<inter> (-b), a) F"  
     using CptnModNestEnv by fastforce  
     moreover have"(n,\<Gamma>,(C, s1)#(C, t1) # xsa) \<in> cptn_mod_nest_call"
       using CptnModNestEnv(1,2) CptnModNestEnv.hyps(1) CptnModNestEnv.hyps(2)
       using cptn_mod_nest_call.CptnModNestEnv by blast
     then have  cptn_mod:"(\<Gamma>,(C, s1)#(C, t1) # xsa) \<in> cptn"    
       using cptn_eq_cptn_mod_nest by blast  
     then have "(\<Gamma>, (C, t1) # xsa) \<in> assum (p, R)"   
       using tl_of_assum_in_assum CptnModNestEnv(6) a1 a2 a3 a4 a5
       by blast
     ultimately have "(\<Gamma>, (C, t1) # xsa) \<in> comm (G, p \<inter> (-b), a) F"
       by auto
     also have " \<not> (\<Gamma>\<turnstile>\<^sub>c((C,s1))  \<rightarrow> ((C,t1)))"
       by (simp add: mod_env_not_component)      
     ultimately show ?case 
       using cptn_mod etran_in_comm by blast
   next 
     case (CptnModNestSkip \<Gamma> C s1 t1 n xsa) 
     then have "C=While b c1" by auto
     also have "(n,\<Gamma>, (LanguageCon.com.Skip, t1) # xsa) \<in> cptn_mod_nest_call"
       using cptn_eq_cptn_mod_set CptnModNestSkip(4) by fastforce
     thus ?case using WhileNone CptnModNestSkip a1 a2 a3 a4 a5  by blast
   next
     case (CptnModNestThrow  \<Gamma> C s1 t1 n xsa) 
     then have "C = While b c1" by auto 
       thus ?case using stepc_elim_cases_while_throw CptnModNestThrow(1) 
       by blast
   next 
     case (CptnModNestWhile1  n \<Gamma> c s1 xs1 b1 xsa zs) 
     then have "b=b1 \<and> c=c1 \<and> s=Normal s1" by auto      
     thus ?case
     using a4 a5 CptnModNestWhile1 while1[of n \<Gamma>] by blast
   next 
     case (CptnModNestWhile2 n \<Gamma> c s1 xs1 b1 xsa ys zs)
     then have a00: "(n,\<Gamma>, (While b c, Normal s1) #
         (Seq c (While b c), Normal s1) # xsa)\<in>cptn_mod_nest_call" 
       using cptn_mod_nest_call.CptnModNestWhile2 by fast   
     then have eqs:"b=b1 \<and> c=c1 \<and> s=Normal s1"using CptnModNestWhile2 by auto
     thus ?case using  a00 a4 a5 CptnModNestWhile2 while2[of n \<Gamma> b c s1 xsa xs1 ys F p R G a] 
       by blast        
   next
     case (CptnModNestWhile3 n \<Gamma> c s1 xs1 b1 sl ys zs)  
     then have eqs:"b=b1 \<and> c=c1 \<and> s=Normal s1" by auto 
     then have "(\<Gamma>, (While b c, Normal s1) #
         (Seq c (While b c), Normal s1) #          
         ((map (lift (While b c)) xs1 @
           (Throw, Normal sl) # ys))) \<in> comm (G, p\<inter>(-b), a) F"        
       using a1 a3 a4 a5 CptnModNestWhile3 while3[of n \<Gamma> c s1 xs1 b sl ys F p R G a] 
       by fastforce   
     thus ?case using eqs CptnModNestWhile3 by auto
   qed (auto)
  }
  then show ?thesis by auto    
qed


lemma While_sound: 
      "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> b, R, G, p,a] \<Longrightarrow>
       (\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> b, R, G, p,a]) \<Longrightarrow>       
       Sta p R \<Longrightarrow>     
       Sta (p \<inter> (-b)) R \<Longrightarrow> Sta a R \<Longrightarrow> \<forall>s. (Normal s, Normal s) \<in> G  \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (While b c1) sat [p, R, G, p \<inter> (-b),a]"
proof -  
  assume
    a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> b, R, G, p,a]" and
    a1:"\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n \<^bsub>/F\<^esub> c1 sat [p \<inter> b, R, G, p,a]" and    
    a2: "Sta p R" and
    a3: "Sta (p \<inter> (-b)) R" and
    a4: "Sta a R" and
    a5: "\<forall>s. (Normal s, Normal s) \<in> G" 
  { 
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"  
    then have a1:"(\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> b, R, G, p,a])" 
      using a1 com_cvalidityn_def by fastforce
    have "cpn n \<Gamma> (While b c1)  s \<inter> assum(p, R) \<subseteq> comm(G, (p \<inter> (-b),a)) F"
    proof-
      {fix c     
        assume a10:"c \<in> cpn n \<Gamma> (While b c1) s" and a11:"c \<in> assum(p, R)"
        then have a10': "c \<in> cp  \<Gamma> (While b c1) s"
          unfolding cp_def cpn_def using cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod by fastforce
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have cp:"l!0=((While b c1),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10' cp_def c_prod by fastforce      
      have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast
      obtain xs where "l=((While b c1),s)#xs" using cp
      proof -
        assume a1: "\<And>xs. l = (LanguageCon.com.While b c1, s) # xs \<Longrightarrow> thesis"
        have "[] \<noteq> l"
          using cp cptn.simps by auto
        then show ?thesis
          using a1 by (metis (full_types) SmallStepCon.nth_tl cp)
      qed 
      moreover have "(n,\<Gamma>,l)\<in>cptn_mod_nest_call" using a10
        using \<Gamma>1 cpn_def by fastforce  
      ultimately have "c \<in> comm(G, (p \<inter> (-b),a)) F"
      using a1 a2 a3 a4   WhileSound_aux a11 \<Gamma>1 a5 
        by blast
      } thus ?thesis by auto qed
  }
  thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def)  
qed


lemma Conseq_sound:
  "(\<forall>s\<in> p.
       \<exists>p' R' G' q' a' I' \<Theta>'.
          s \<in> p' \<and>
          R \<subseteq> R' \<and>            
          G' \<subseteq> G \<and>             
          q' \<subseteq> q \<and>
          a' \<subseteq> a \<and> \<Theta>' \<subseteq> \<Theta> \<and>
          \<Gamma>,\<Theta>' \<turnstile>\<^bsub>/F\<^esub> P sat [p',R', G', q',a'] \<and> 
          (\<forall>n. \<Gamma>,\<Theta>' \<Turnstile>n\<^bsub>/F\<^esub> P sat [p', R', G', q',a'])) \<Longrightarrow>
  \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> P sat [p,R, G, q,a]" 
proof -
  assume 
  a0: "(\<forall>s\<in> p.
       \<exists>p' R' G' q' a' I' \<Theta>'.
          s \<in> p' \<and>
          R \<subseteq> R' \<and>            
          G' \<subseteq> G \<and>             
          q' \<subseteq> q \<and>
          a' \<subseteq> a \<and> \<Theta>' \<subseteq> \<Theta> \<and>
          \<Gamma>,\<Theta>' \<turnstile>\<^bsub>/F\<^esub> P sat [p',R', G', q',a'] \<and> 
          (\<forall>n. \<Gamma>,\<Theta>' \<Turnstile>n\<^bsub>/F\<^esub> P sat [p', R', G', q',a']))"
  {
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"
    have "cpn n \<Gamma> P  s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
    proof -
    {
      fix c
      assume a10:"c \<in> cpn n \<Gamma> P s" and a11:"c \<in> assum(p, R)"
      then have a10':"c\<in>cp \<Gamma> P s" unfolding cp_def cpn_def cptn_eq_cptn_mod_nest by auto
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have cp:"l!0=(P,s) \<and> (n,\<Gamma>,l) \<in> cptn_mod_nest_call \<and> \<Gamma>=\<Gamma>1" using a10 cpn_def c_prod by fastforce
      have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast 
      obtain xs where "l=(P,s)#xs" using cp
      proof -
        assume a1: "\<And>xs. l = (P, s) # xs \<Longrightarrow> thesis"
        have "[] \<noteq> l"
          using cp cptn.simps
          using CptnEmpty by force
        then show ?thesis
          using a1 by (metis (full_types) SmallStepCon.nth_tl cp)
      qed
      obtain ns where s:"(s = Normal ns)" using a10 a11 unfolding assum_def cpn_def by fastforce
      then have "ns \<in> p" using a10 a11 unfolding assum_def cpn_def by fastforce
      then have ns:"ns\<in>p" by auto
      then have
      "\<forall>s. s \<in> p \<longrightarrow> (\<exists>p' R' G' q' a' \<Theta>'. (s\<in>p') \<and>
        R \<subseteq> R' \<and>            
        G' \<subseteq> G \<and>             
        q' \<subseteq> q \<and>
        a' \<subseteq> a \<and> \<Theta>' \<subseteq> \<Theta> \<and>
        (\<Gamma>,\<Theta>' \<turnstile>\<^bsub>/F\<^esub> P sat [p',R', G', q',a']) \<and> 
        (\<forall>n. \<Gamma>,\<Theta>' \<Turnstile>n\<^bsub>/F\<^esub> P sat [p', R', G', q',a']))" using a0 by auto
      then have 
       "ns \<in> p \<longrightarrow> (\<exists>p' R' G' q' a' \<Theta>'. (ns \<in> p' ) \<and>
        R \<subseteq> R' \<and>            
        G' \<subseteq> G \<and>             
        q' \<subseteq> q \<and>
        a' \<subseteq> a \<and> \<Theta>' \<subseteq> \<Theta> \<and>
        (\<Gamma>,\<Theta>' \<turnstile>\<^bsub>/F\<^esub> P sat [p',R', G', q',a']) \<and> 
        (\<forall>n. \<Gamma>,\<Theta>' \<Turnstile>n\<^bsub>/F\<^esub> P sat [p', R', G', q',a']))" apply (rule allE) by auto     
     then obtain p' R' G' q' a' \<Theta>'   where
     rels:
       "ns \<in> p' \<and>
        R \<subseteq> R' \<and>            
        G' \<subseteq> G \<and>             
        q' \<subseteq> q \<and>
        a' \<subseteq> a \<and> \<Theta>' \<subseteq> \<Theta> \<and>       
        (\<forall>n. \<Gamma>,\<Theta>' \<Turnstile>n\<^bsub>/F\<^esub> P sat [p', R', G', q',a'])" using ns by auto
      then have "s \<in>  Normal ` p'" using s by fastforce
      then have "(\<Gamma>,l) \<in> assum(p', R')"
        using a11 rels cp a11 c_prod assum_R_R'[of \<Gamma> l p R p' R'] 
        by fastforce
      then have "(\<Gamma>,l) \<in> comm(G',(q',a')) F" 
        using rels all_call a10 c_prod cp unfolding com_cvalidityn_def com_validityn_def 
        by blast
      then have "(\<Gamma>,l) \<in> comm(G, (q,a)) F" 
        using c_prod cp comm_conseq[of \<Gamma> l G' q' a' F G q a] rels by fastforce
      then have "c \<in> comm(G, (q,a)) F" using c_prod cp by fastforce
    }                 
    thus ?thesis unfolding comm_def by force qed      
  } thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def)  
qed   

lemma Conj_post_sound:
  "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p,R, G, q,a] \<and> 
   (\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> P sat [p, R, G, q,a]) \<Longrightarrow> 
   \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p,R, G, q',a'] \<and> 
   (\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n \<^bsub>/F\<^esub> P sat [p, R, G, q',a']) \<Longrightarrow>
  \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> P sat [p,R, G, q \<inter> q' ,a \<inter> a']" 
proof -
assume a0: "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p,R, G, q,a] \<and> 
   (\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> P sat [p, R, G, q,a])" and
       a1: " \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p,R, G, q',a'] \<and> 
   (\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n \<^bsub>/F\<^esub> P sat [p, R, G, q',a'])"
{
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"
    with a0 have a0:"cpn n \<Gamma> P  s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
      unfolding com_cvalidityn_def com_validityn_def by auto
    with a1 all_call have a1:"cpn n \<Gamma> P  s \<inter> assum(p, R) \<subseteq> comm(G, (q',a')) F"
      unfolding com_cvalidityn_def com_validityn_def by auto
    have "cpn n \<Gamma> P  s \<inter> assum(p, R) \<subseteq> comm(G, (q\<inter>q',a\<inter>a')) F"
    proof -
    {
      fix c
      assume a10:"c \<in> cpn n \<Gamma> P s" and a11:"c \<in> assum(p, R)"
      then have "c \<in> comm(G,(q,a)) F \<and> c \<in> comm(G,(q',a')) F"
        using a0 a1 by auto
      then have  "c\<in>comm(G, (q\<inter>q',a\<inter>a')) F"
        unfolding comm_def by fastforce
    }               
    thus ?thesis unfolding comm_def by force qed      
  } thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def)  
qed  
  
lemma x91:"sa\<noteq>{} \<Longrightarrow> c\<in>comm(G, (\<Inter>i\<in>sa. q i,a)) F  = (\<forall>i\<in>sa. c\<in>comm(G, q i,a) F)"    
  unfolding comm_def apply (auto simp add: Ball_def) 
   apply (frule spec ,  force)
    by (frule spec,  force)

  
  
lemma conj_inter_sound:
"sa \<noteq> {} \<Longrightarrow> 
 \<forall>i\<in>sa. \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q i,a] \<and> (\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> P sat [p,R, G, q i,a]) \<Longrightarrow> 
 \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> P sat [p,R, G, \<Inter>i\<in>sa. q i,a]"
proof -
  assume a0':"sa\<noteq>{}" and 
         a0: "\<forall>i\<in>sa. \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q i,a] \<and> 
              (\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> P sat [p,R, G, q i,a])" 
{
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"
    with a0 have a0:"\<forall>i\<in>sa. cpn n \<Gamma> P  s \<inter> assum(p, R) \<subseteq> comm(G, (q i,a)) F"
      unfolding com_cvalidityn_def com_validityn_def by auto    
    have "cpn n \<Gamma> P  s \<inter> assum(p, R) \<subseteq> comm(G, (\<Inter>i\<in>sa. q i,a)) F"
    proof -
    {
      fix c
      assume a10:"c \<in> cpn n \<Gamma> P s" and a11:"c \<in> assum(p, R)"        
      then have  "(\<forall>i\<in>sa. c\<in>comm(G, q i,a) F)"        
        using a0 by fastforce
      then have "c\<in>comm(G, (\<Inter>i\<in>sa. q i,a)) F" using x91[OF a0'] by blast
    }               
    thus ?thesis unfolding comm_def by force qed      
  } thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def)  
qed     

lemma localRG_sound: "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p, R, G, q,a] \<Longrightarrow> (\<And>n. \<Gamma>,\<Theta> \<Turnstile>n \<^bsub>/F\<^esub> c sat [p, R, G, q,a])"
proof (induct rule:lrghoare.induct)
  case Skip 
    thus ?case  by (simp add: Skip_sound)
next
  case Spec
    thus ?case  by (simp add: Spec_sound)
next
  case Basic
    thus ?case by (simp add: Basic_sound)
next
  case Await
    thus ?case by (simp add: Await_sound)
next
  case Throw thus ?case by (simp add: Throw_sound)
next 
  case If thus ?case using If_sound by (simp add: If_sound)
next
  case Asm thus ?case by (simp add: Asm_sound)
next 
  case CallRec thus ?case  by (simp add: CallRec_sound)
next
  case Call thus ?case using Call_sound  by (simp add: Call_sound)
next
  case Seq thus ?case by (simp add: Seq_sound)
next
  case Catch thus ?case by (simp add: Catch_sound)
next
  case DynCom thus ?case by (simp add: DynCom_sound)
next
  case Guard thus ?case by (simp add: Guard_sound)
next
  case Guarantee thus ?case by (simp add: Guarantee_sound)
next
  case While thus ?case by (simp add: While_sound)
next
  case (Conseq p R G q a \<Gamma> \<Theta> F P) thus ?case 
    using Conseq_sound by simp
next 
  case (Conj_post \<Gamma> \<Theta> F P p' R' G' q a q' a') thus ?case
    using Conj_post_sound[of \<Gamma> \<Theta>] by simp
next
  case (Conj_Inter sa \<Gamma> \<Theta> F P p' R' G' q a ) 
    thus ?case using conj_inter_sound[of sa \<Gamma> \<Theta>] by simp 
qed   


definition ParallelCom :: "('s,'p,'f,'e) rgformula list \<Rightarrow> ('s,'p,'f,'e) par_com"
where
"ParallelCom Ps \<equiv> map fst Ps"

lemma ParallelCom_Com:"i<length xs \<Longrightarrow> (ParallelCom xs)!i = Com (xs!i)"
unfolding ParallelCom_def Com_def by fastforce


lemma etran_ctran_eq_p_normal_s: "\<Gamma>\<turnstile>\<^sub>c s1  \<rightarrow> s1' \<Longrightarrow>
             \<Gamma>\<turnstile>\<^sub>c s1  \<rightarrow>\<^sub>e s1' \<Longrightarrow>
            fst s1 = fst s1' \<and> snd s1 = snd s1' \<and> (\<exists>ns1. snd s1 = Normal ns1)"
proof -
   assume a0: "\<Gamma>\<turnstile>\<^sub>c s1  \<rightarrow> s1'" and
          a1: "\<Gamma>\<turnstile>\<^sub>c s1  \<rightarrow>\<^sub>e s1'"
   then obtain ps1 ss1 ps1' ss1' where prod:"s1 = (ps1,ss1) \<and> s1' = (ps1', ss1')"
     by fastforce
   then have "ps1=ps1'" using a1 etranE by fastforce
   thus ?thesis using prod  a0 by (simp add: mod_env_not_component)
qed

lemma step_e_step_c_eq:"\<lbrakk> 
  (\<Gamma>,l) \<propto> clist;
  Suc m < length l;
  i < length clist; 
  (fst (clist!i))\<turnstile>\<^sub>c((snd (clist!i))!m) \<rightarrow>\<^sub>e  ((snd (clist!i))!Suc m);          
  (fst (clist!i))\<turnstile>\<^sub>c((snd (clist!i))!m) \<rightarrow>  ((snd (clist!i))!Suc m);
  (\<forall>l<length clist. 
     l\<noteq>i \<longrightarrow>  (fst (clist!l))\<turnstile>\<^sub>c (snd (clist!l))!m  \<rightarrow>\<^sub>e ((snd (clist!l))!(Suc m)))
  \<rbrakk> \<Longrightarrow> 
  l!m = l!(Suc m) \<and> (\<exists>ns. snd (l!m) = Normal ns )"
proof -
  assume a0:"(\<Gamma>,l) \<propto> clist" and
         a1:"Suc m < length l" and
         a2:"i < length clist" and
         a3:"(fst (clist!i))\<turnstile>\<^sub>c((snd (clist!i))!m) \<rightarrow>\<^sub>e  ((snd (clist!i))!Suc m)" and
         a4:"(fst (clist!i))\<turnstile>\<^sub>c((snd (clist!i))!m) \<rightarrow>  ((snd (clist!i))!Suc m)" and
         a5:"(\<forall>l<length clist. 
                 l\<noteq>i \<longrightarrow> (fst (clist!l))\<turnstile>\<^sub>c (snd (clist!l))!m  \<rightarrow>\<^sub>e ((snd (clist!l))!(Suc m)))"
  obtain fp fs sp ss 
    where prod_step: " 
               \<Gamma>\<turnstile>\<^sub>c (fp, fs) \<rightarrow> (sp,ss) \<and> 
              fp = fst (((snd (clist!i))!m)) \<and> fs = snd (((snd (clist!i))!m)) \<and> 
              sp = fst ((snd (clist!i))!(Suc m)) \<and> ss = snd((snd (clist!i))!(Suc m)) \<and>
              \<Gamma> = fst (clist!i)"
    using a0 a2 a1 a4 unfolding conjoin_def same_functions_def by fastforce 
  have snd_lj:"(snd (l!m)) = snd ((snd (clist!i))!m)"
            using a0 a1 a2  unfolding conjoin_def same_state_def
            by fastforce 
  have fst_clist_\<Gamma>:"\<forall>i<length clist. fst(clist!i) = \<Gamma>" 
    using a0 unfolding conjoin_def same_functions_def by fastforce
  have all_env: "\<forall>l<length clist. 
                    (fst (clist!l))\<turnstile>\<^sub>c (snd (clist!l))!m  \<rightarrow>\<^sub>e ((snd (clist!l))!(Suc m))"
    using a3 a5 a2 fst_clist_\<Gamma> by fastforce
  then have allP:"\<forall>l< length clist. fst ((snd (clist!l))!m) = fst ((snd (clist!l))!(Suc m))"
    by (fastforce elim:etranE)         
  then have "fst (l!m) = (fst (l!(Suc m)))"
    using a0 conjoin_same_program_i_j [of "(\<Gamma>,l)"] a1 by fastforce
  also have snd_l_normal:"snd (l!m) = snd (l!(Suc m)) \<and> (\<exists>ns. snd (l!m) = Normal ns )"
  proof -                        
    have "(snd (l!Suc m)) = snd ((snd (clist!i))!(Suc m))"
      using a0 a1 a2 unfolding conjoin_def same_state_def
      by fastforce
    also have "fs = ss \<and> 
               (\<exists>ns.  (snd ((snd (clist!i))!m) = Normal ns ))"
      using a1 a2  all_env prod_step allP
      by (metis step_change_p_or_eq_s)       
    ultimately show ?thesis using snd_lj prod_step a1  by fastforce
  qed 
  ultimately show ?thesis using prod_eq_iff by blast      
qed

lemma two': 
  "\<lbrakk> \<forall>i<length xs. R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Guar (xs ! j)))
       \<subseteq> (Rely (xs ! i));
   p \<subseteq> (\<Inter>i<length xs. (Pre (xs ! i)));
   \<forall>i<length xs.
    \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Com (xs ! i) sat [Pre (xs!i), Rely (xs ! i), Guar (xs ! i), Post (xs ! i),Abr (xs ! i)];
   length xs=length clist; (\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s; (\<Gamma>,l)\<in>par_assum (p, R) ;
  \<forall>i<length clist. clist!i\<in>cp \<Gamma> (Com(xs!i)) s; (\<Gamma>,l) \<propto> clist;(\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]);
  snd (last l) \<notin> Fault ` F\<rbrakk>
  \<Longrightarrow> \<forall>j i ns ns'. i<length clist \<and> Suc j<length l \<longrightarrow> 
      \<Gamma>\<turnstile>\<^sub>c((snd (clist!i))!j) \<rightarrow>\<^sub>e  ((snd (clist!i))!Suc j) \<longrightarrow> 
      (snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in> Rely(xs!i)"
proof -
  assume a0:"\<forall>i<length xs. R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Guar (xs ! j)))
       \<subseteq> (Rely (xs ! i))" and
         a1:"p \<subseteq> (\<Inter>i<length xs. (Pre (xs ! i)))" and
         a2:"\<forall>i<length xs.
    \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Com (xs ! i) sat [Pre (xs!i), Rely (xs ! i), Guar (xs ! i), Post (xs ! i),Abr (xs ! i)]" and
         a3: "length xs=length clist" and
         a4: "(\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s" and
         a5: "(\<Gamma>,l)\<in>par_assum (p, R)" and
         a6: "\<forall>i<length clist. clist!i\<in>cp \<Gamma> (Com(xs!i)) s" and
         a7: "(\<Gamma>,l) \<propto> clist" and
         a8: "(\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a])" and 
         a9: "snd (last l) \<notin> Fault ` F"
{
  assume a10:"\<exists>i j ns ns'. 
              i<length clist \<and> Suc j<length l \<and> 
              \<Gamma>\<turnstile>\<^sub>c((snd (clist!i))!j) \<rightarrow>\<^sub>e  ((snd (clist!i))!Suc j) \<and> 
              \<not>(snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in> Rely(xs!i)"
  then obtain j where 
    a10:"\<exists>i ns ns'. 
       i<length clist \<and> Suc j<length l \<and> 
       \<Gamma>\<turnstile>\<^sub>c((snd (clist!i))!j) \<rightarrow>\<^sub>e  ((snd (clist!i))!Suc j) \<and>
       \<not>(snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in> Rely(xs!i)" by fastforce
   let ?P = "\<lambda>j. \<exists>i. i<length clist \<and> Suc j<length l \<and>
      \<Gamma>\<turnstile>\<^sub>c((snd (clist!i))!j) \<rightarrow>\<^sub>e  ((snd (clist!i))!Suc j) \<and>       
      (\<not> (snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in> Rely(xs!i))"        
   obtain m where fist_occ:"(?P m) \<and> (\<forall>i<m. \<not> ?P i)" using exists_first_occ[of ?P j] a10 by blast
     then have "?P m" by fastforce
     then obtain i where
      fst_occ:"i<length clist \<and> Suc m<length l \<and>
      \<Gamma>\<turnstile>\<^sub>c((snd (clist!i))!m) \<rightarrow>\<^sub>e  ((snd (clist!i))!Suc m) \<and>       
      (\<not> (snd((snd (clist!i))!m), snd((snd (clist!i))!Suc m)) \<in> Rely(xs!i))"
     by fastforce
    have notP:"(\<forall>i<m. \<not> ?P i)" using fist_occ by blast     
    have fst_clist_\<Gamma>:"\<forall>i<length clist. fst(clist!i) = \<Gamma>" 
      using a7 unfolding conjoin_def same_functions_def by fastforce
    have compat:"(\<Gamma>\<turnstile>\<^sub>p(l!m)  \<rightarrow> (l!(Suc m))) \<and> 
            (\<exists>i<length clist. 
               ((fst (clist!i))\<turnstile>\<^sub>c ((snd (clist!i))!m)  \<rightarrow> ((snd (clist!i))!(Suc m))) \<and> 
            (\<forall>l<length clist. 
               l\<noteq>i \<longrightarrow>  (fst (clist!l))\<turnstile>\<^sub>c (snd (clist!l))!m  \<rightarrow>\<^sub>e ((snd (clist!l))!(Suc m)))) \<or> 
         (\<Gamma>\<turnstile>\<^sub>p(l!m)  \<rightarrow>\<^sub>e (l!(Suc m)) \<and> 
          (\<forall>i<length clist.  (fst (clist!i))\<turnstile>\<^sub>c (snd (clist!i))!m  \<rightarrow>\<^sub>e ((snd (clist!i))!(Suc m))))"
     using a7 fst_occ unfolding conjoin_def compat_label_def by simp
     {
       assume a20: "(\<Gamma>\<turnstile>\<^sub>p(l!m)  \<rightarrow>\<^sub>e (l!(Suc m)) \<and> 
          (\<forall>i<length clist.  (fst (clist!i))\<turnstile>\<^sub>c (snd (clist!i))!m  \<rightarrow>\<^sub>e ((snd (clist!i))!(Suc m))))"
       then have "(snd (l!m),snd (l!(Suc m))) \<in> R"       
       using fst_occ a5  unfolding par_assum_def by fastforce
       then have "(snd(l!m), snd(l!(Suc m))) \<in>  Rely(xs!i)"
       using fst_occ a3 a0 by fastforce
       then have "(snd ((snd (clist!i))!m), snd ((snd (clist!i))!(Suc m)) ) \<in>  Rely(xs!i)" 
       using a7 fst_occ unfolding conjoin_def same_state_def by fastforce        
       then have False using fst_occ by auto
     }note l = this
     {
      assume a20:"(\<Gamma>\<turnstile>\<^sub>p(l!m)  \<rightarrow> (l!(Suc m))) \<and> 
            (\<exists>i<length clist. 
               ((fst (clist!i))\<turnstile>\<^sub>c ((snd (clist!i))!m)  \<rightarrow> ((snd (clist!i))!(Suc m))) \<and> 
            (\<forall>l<length clist. 
               l\<noteq>i \<longrightarrow>  (fst (clist!l))\<turnstile>\<^sub>c (snd (clist!l))!m  \<rightarrow>\<^sub>e ((snd (clist!l))!(Suc m))))"
      then obtain i'  
      where i':"i'<length clist \<and> 
               ((fst (clist!i'))\<turnstile>\<^sub>c ((snd (clist!i'))!m)  \<rightarrow> ((snd (clist!i'))!(Suc m))) \<and> 
               (\<forall>l<length clist. 
                 l\<noteq>i' \<longrightarrow>  (fst (clist!l))\<turnstile>\<^sub>c (snd (clist!l))!m  \<rightarrow>\<^sub>e ((snd (clist!l))!(Suc m)))"
      by fastforce
      then have eq_\<Gamma>:"\<Gamma> = fst (clist!i')" using a7 unfolding conjoin_def same_functions_def by fastforce
      obtain fp fs sp ss 
      where prod_step: " 
               \<Gamma>\<turnstile>\<^sub>c (fp, fs) \<rightarrow> (sp,ss) \<and> 
              fp = fst (((snd (clist!i'))!m)) \<and> fs = snd (((snd (clist!i'))!m)) \<and> 
              sp = fst ((snd (clist!i'))!(Suc m)) \<and> ss = snd((snd (clist!i'))!(Suc m)) \<and>
              \<Gamma> = fst (clist!i') "
      using a7 i' unfolding conjoin_def same_functions_def by fastforce            
      then have False
      proof (cases "i = i'")
        case True       
        then have "l!m = l!(Suc m) \<and> (\<exists>ns. snd (l!m) = Normal ns )"
          using step_e_step_c_eq[OF a7] i' fst_occ eq_\<Gamma> by blast
        then have "\<Gamma>\<turnstile>\<^sub>p(l!m)  \<rightarrow>\<^sub>e (l!(Suc m))" 
          using step_pe.ParEnv  by (metis prod.collapse)           
        then have "(snd (l ! m), snd (l ! Suc m)) \<in> R "
          using fst_occ  a5 unfolding par_assum_def by fastforce
        then have "(snd (l ! m), snd (l ! Suc m)) \<in> Rely (xs ! i)"
          using a0 a3 fst_occ by fastforce
        then show ?thesis using fst_occ a7
          unfolding conjoin_def same_state_def  
          by fastforce         
      next
        case False  note not_eq = this       
        thus ?thesis 
        proof (cases "fp = sp")
          case True 
          then have  "fs = ss \<and> (\<exists>ns. fs=Normal ns)" 
            using prod_step  prod_step
            using step_change_p_or_eq_s by blast  
          
          then have "\<Gamma>\<turnstile>\<^sub>c (fp, fs) \<rightarrow>\<^sub>e (sp, ss)" using True step_e.Env 
            by fastforce
          then have "l!m = l!(Suc m) \<and> (\<exists>ns. snd (l!m) = Normal ns )"
            using step_e_step_c_eq[OF a7] prod_step i' fst_occ prod.collapse by auto
          then have "\<Gamma>\<turnstile>\<^sub>p(l!m)  \<rightarrow>\<^sub>e (l!(Suc m))" 
            using step_pe.ParEnv  by (metis prod.collapse)           
          then have "(snd (l ! m), snd (l ! Suc m)) \<in> R "
            using fst_occ  a5 unfolding par_assum_def by fastforce
          then have "(snd (l ! m), snd (l ! Suc m)) \<in> Rely (xs ! i)"
            using a0 a3 fst_occ by fastforce
          then show ?thesis using fst_occ a7
            unfolding conjoin_def same_state_def  
          by fastforce                   
        next
          case False                    
          let ?l1 = "take (Suc (Suc m)) (snd(clist!i'))"
          have clist_cptn:"(\<Gamma>,snd(clist!i')) \<in> cptn" using a6 i' unfolding cp_def by fastforce
          have sucm_len:"Suc m < length (snd (clist!i'))" 
            using i' fst_occ a7 unfolding conjoin_def same_length_def by fastforce          
          then have summ_lentake:"Suc m < length ?l1" by fastforce
          have len_l: "0<length l" using fst_occ by fastforce
          also then have "snd (clist!i')\<noteq>[]" 
            using i' a7 unfolding conjoin_def same_length_def by fastforce
          ultimately have "snd (last (snd (clist ! i'))) = snd (last l)"
            using a7 i' conjoin_last_same_state by fastforce
          then have last_i_notF:"snd (last (snd(clist!i'))) \<notin> Fault ` F" 
            using a9 by auto  
          have "\<forall>i<length (snd(clist!i')).  snd (snd(clist!i') ! i) \<notin> Fault ` F " 
            using  last_not_F[OF clist_cptn last_i_notF] by auto 
          also have suc_m_i':"Suc m < length (snd (clist !i'))"
            using fst_occ i' a7 unfolding conjoin_def same_length_def by fastforce
          ultimately have last_take_not_f:"snd (last (take (Suc (Suc m)) (snd(clist!i')))) \<notin> Fault ` F"
            by (simp add: take_Suc_conv_app_nth)           
          have not_env_step:"\<not> \<Gamma>\<turnstile>\<^sub>c snd (clist ! i') ! m \<rightarrow>\<^sub>e snd (clist ! i') ! Suc m"
            using False etran_ctran_eq_p_normal_s i' prod_step by blast           
          then have "snd ((snd(clist!i'))!0)\<in> Normal ` p" 
            using len_l a7 i' a5 unfolding conjoin_def same_state_def par_assum_def by fastforce
          then have "snd ((snd(clist!i'))!0)\<in> Normal ` (Pre (xs ! i'))"
            using a1 i' a3 by fastforce
          then have "snd ((take (Suc (Suc m)) (snd(clist!i')))!0)\<in> Normal `(Pre (xs ! i'))" 
            by fastforce       
          moreover have 
          "\<forall>j. Suc j < Suc (Suc m) \<longrightarrow>
                \<Gamma>\<turnstile>\<^sub>c snd (clist ! i') ! j \<rightarrow>\<^sub>e snd (clist ! i') ! Suc j \<longrightarrow>
                (snd (snd (clist ! i') ! j), snd (snd (clist ! i') ! Suc j)) \<in> Rely (xs ! i')" 
            using not_env_step fst_occ Suc_less_eq fist_occ i' less_SucE less_trans_Suc by auto
          then have "\<forall>j. Suc j < length (take (Suc (Suc m)) (snd(clist!i'))) \<longrightarrow>
                \<Gamma>\<turnstile>\<^sub>c snd (clist ! i') ! j \<rightarrow>\<^sub>e snd (clist ! i') ! Suc j \<longrightarrow>
                (snd (snd (clist ! i') ! j), snd (snd (clist ! i') ! Suc j)) \<in> Rely (xs ! i')"
            by fastforce 
          ultimately have "(\<Gamma>, (take (Suc (Suc m)) (snd(clist!i')))) \<in> 
                             assum ((Pre (xs ! i')),Rely (xs ! i'))"
            unfolding assum_def by fastforce         
          moreover have "(\<Gamma>,snd(clist!i')) \<in> cptn" using a6 i' unfolding cp_def by fastforce
          then have "(\<Gamma>,take (Suc (Suc m)) (snd(clist!i'))) \<in> cptn"
            by (simp add: takecptn_is_cptn)              
          then have "(\<Gamma>,take (Suc (Suc m)) (snd(clist!i'))) \<in> cp \<Gamma> (Com(xs!i')) s"
            using i' a3 a6 unfolding cp_def by fastforce          
          ultimately have t:"(\<Gamma>,take (Suc (Suc m)) (snd(clist!i'))) \<in> 
                              comm (Guar (xs ! i'), (Post (xs ! i'),Abr (xs ! i'))) F "
          using a8 a2 a3 i' unfolding com_cvalidity_def com_validity_def by fastforce               
          have "(snd(take (Suc (Suc m)) (snd(clist!i'))!m), 
                        snd(take (Suc (Suc m)) (snd(clist!i'))!(Suc m))) \<in> Guar (xs ! i')"
            using eq_\<Gamma>  i' comm_dest1[OF t last_take_not_f summ_lentake] by fastforce
          
          then have "(snd( (snd(clist!i'))!m), 
                        snd((snd(clist!i'))!(Suc m))) \<in> Guar (xs ! i')"
          by fastforce
          then have "(snd( (snd(clist!i))!m), 
                      snd((snd(clist!i))!(Suc m))) \<in> Guar (xs ! i')"
           using a7 fst_occ unfolding conjoin_def same_state_def by (metis Suc_lessD i' snd_conv) 
          then have "(snd( (snd(clist!i))!m), 
                      snd((snd(clist!i))!(Suc m))) \<in> Rely (xs ! i)"
          using not_eq a0 i' a3 fst_occ by auto          
          then have "False" using fst_occ by auto
          then show ?thesis by auto
        qed
      qed
     }  
  then have False using compat l by auto
} thus ?thesis by auto
qed

lemma two: 
  "\<lbrakk> \<forall>i<length xs. R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Guar (xs ! j)))
       \<subseteq> (Rely (xs ! i));
   p \<subseteq> (\<Inter>i<length xs. (Pre (xs ! i)));
   \<forall>i<length xs.
    \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Com (xs ! i) sat [Pre (xs!i), Rely (xs ! i), Guar (xs ! i), Post (xs ! i),Abr (xs ! i)];
   length xs=length clist; (\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s; (\<Gamma>,l)\<in>par_assum (p, R);
  \<forall>i<length clist. clist!i\<in>cp \<Gamma> (Com(xs!i)) s; (\<Gamma>,l) \<propto> clist;(\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]);
  snd (last l) \<notin> Fault ` F\<rbrakk>
  \<Longrightarrow> \<forall>j i ns ns'. i<length clist \<and> Suc j<length l \<longrightarrow> 
      \<Gamma>\<turnstile>\<^sub>c((snd (clist!i))!j) \<rightarrow>  ((snd (clist!i))!Suc j) \<longrightarrow>       
        (snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in> Guar(xs!i) "
proof -
  assume a0:"\<forall>i<length xs. R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Guar (xs ! j)))
       \<subseteq> (Rely (xs ! i))" and
         a1:"p \<subseteq> (\<Inter>i<length xs. (Pre (xs ! i)))" and
         a2:"\<forall>i<length xs.
    \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Com (xs ! i) sat [Pre (xs!i), Rely (xs ! i), Guar (xs ! i), Post (xs ! i),Abr (xs ! i)]" and
         a3: "length xs=length clist" and
         a4: "(\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s" and
         a5: "(\<Gamma>,l)\<in>par_assum (p, R)" and
         a6: "\<forall>i<length clist. clist!i\<in>cp \<Gamma> (Com(xs!i)) s" and
         a7: "(\<Gamma>,l) \<propto> clist" and
         a8: "(\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a])" and 
         a9: "snd (last l) \<notin> Fault ` F"
  {
     assume a10:"(\<exists>i j. i<length clist \<and> Suc j<length l \<and>  
      \<Gamma>\<turnstile>\<^sub>c((snd (clist!i))!j) \<rightarrow>  ((snd (clist!i))!Suc j) \<and> 
       \<not> (snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in> Guar(xs!i)) "
     then obtain j where a10: "\<exists>i. i<length clist \<and> Suc j<length l \<and>
      \<Gamma>\<turnstile>\<^sub>c((snd (clist!i))!j) \<rightarrow>  ((snd (clist!i))!Suc j) \<and>        
      \<not> (snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in> Guar(xs!i)"
     by fastforce
     let ?P = "\<lambda>j. \<exists>i. i<length clist \<and> Suc j<length l \<and>
      \<Gamma>\<turnstile>\<^sub>c((snd (clist!i))!j) \<rightarrow>  ((snd (clist!i))!Suc j) \<and>       
      \<not> (snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in> Guar(xs!i)"     
     obtain m where fist_occ:"?P m \<and> (\<forall>i<m. \<not> ?P i)" using exists_first_occ[of ?P j] a10 by blast
     then have P:"?P m" by fastforce
     then have notP:"(\<forall>i<m. \<not> ?P i)" using fist_occ by blast
     obtain i ns ns' where fst_occ:"i<length clist \<and> Suc m<length l \<and> 
      \<Gamma>\<turnstile>\<^sub>c((snd (clist!i))!m) \<rightarrow>  ((snd (clist!i))!Suc m) \<and>      
      (\<not> (snd((snd (clist!i))!m), snd((snd (clist!i))!Suc m)) \<in>  Guar(xs!i))"
       using P by fastforce
     have fst_clist_i: "fst (clist!i) = \<Gamma>" 
         using a7 fst_occ unfolding conjoin_def same_functions_def 
         by fastforce
     have "clist!i\<in>cp \<Gamma> (Com(xs!i)) s" using a6 fst_occ by fastforce
     then have clistcp:"(\<Gamma>, snd (clist!i))\<in>cp \<Gamma> (Com(xs!i)) s" 
         using  fst_occ a7 unfolding conjoin_def same_functions_def by fastforce
     let ?li="take (Suc (Suc m)) (snd (clist!i))"     
     have "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub>  Com (xs ! i) sat [Pre (xs!i), Rely (xs ! i), Guar (xs ! i), Post (xs ! i),Abr (xs ! i)]"
       using a8 a2 a3 fst_occ unfolding com_cvalidity_def by fastforce
     moreover have take_in_ass:"(\<Gamma>, take (Suc (Suc m)) (snd (clist!i))) \<in> assum (Pre(xs!i), Rely(xs!i))"     
     proof -
       have length_take_length_l:"length (take (Suc (Suc m)) (snd (clist!i))) \<le> length l"
         using a7 fst_occ unfolding conjoin_def same_length_def by auto
       have "snd((?li!0)) \<in> Normal ` Pre(xs!i)" 
       proof -
         have "(take (Suc (Suc m)) (snd (clist!i)))!0 = (snd (clist!i))!0" by fastforce
         moreover have "snd (snd(clist!i)!0) = snd (l!0)" 
           using a7 fst_occ unfolding conjoin_def same_state_def by fastforce
         moreover have "snd (l!0) \<in> Normal ` p" 
           using a5 unfolding par_assum_def by fastforce
         ultimately show ?thesis using a1 a3 fst_occ by fastforce 
       qed note left=this
       thus ?thesis  
         using two'[OF a0 a1 a2 a3 a4 a5 a6 a7 a8 a9] fst_occ unfolding assum_def by fastforce
       qed     
     moreover have "(\<Gamma>,take (Suc (Suc m)) (snd (clist!i))) \<in> cp \<Gamma> (Com(xs!i)) s"
       using takecptn_is_cptn clistcp unfolding cp_def by fastforce      
     ultimately have comm:"(\<Gamma>, take (Suc (Suc m)) (snd (clist!i)))\<in>comm(Guar(xs!i),(Post (xs ! i),Abr (xs ! i))) F"       
        unfolding com_validity_def by fastforce  
     also have not_fault:"snd (last (take (Suc (Suc m)) (snd (clist!i))))  \<notin> Fault ` F"
     proof -      
       have cptn:"(\<Gamma>, snd (clist!i)) \<in> cptn" 
         using fst_clist_i a6 fst_occ unfolding cp_def by fastforce   
       then have "(snd (clist!i))\<noteq>[]" 
        using cptn.simps list.simps(3) 
        by fastforce               
       then have "snd (last (snd (clist!i))) = snd (last l)"
         using conjoin_last_same_state fst_occ a7 by fastforce
       then have "snd (last (snd (clist!i))) \<notin> Fault ` F" using a9
         by simp
       also have sucm:"Suc m < length (snd (clist!i))" 
         using fst_occ a7 unfolding conjoin_def same_length_def by fastforce
       ultimately have sucm_not_fault:"snd ((snd (clist!i))!(Suc m)) \<notin> Fault ` F"
         using last_not_F cptn by blast 
       have "length (take (Suc (Suc m)) (snd (clist!i))) = Suc (Suc m)" 
         using sucm by fastforce
       then have "last (take (Suc (Suc m)) (snd (clist!i))) =  (take (Suc (Suc m)) (snd (clist!i)))!(Suc m)"
         by (metis Suc_diff_1 Suc_inject last_conv_nth list.size(3) old.nat.distinct(2) zero_less_Suc)
       moreover have "(take (Suc (Suc m)) (snd (clist!i)))!(Suc m) = (snd (clist!i))!(Suc m)" 
         by fastforce      
       ultimately show ?thesis using sucm_not_fault by fastforce
     qed
     then have " (Suc m < length (snd (clist ! i)) ) \<longrightarrow>
                 (\<Gamma>\<turnstile>\<^sub>c (snd (clist ! i)) ! m \<rightarrow> (snd (clist ! i)) ! Suc m) \<longrightarrow>                      
                    (snd ((snd (clist ! i)) ! m), snd ((snd (clist ! i)) ! Suc m)) \<in> Guar(xs!i)"
       using comm_dest [OF comm not_fault] by auto     
     then have "False" using fst_occ using a7 unfolding conjoin_def same_length_def by fastforce
  } thus ?thesis by fastforce
qed

lemma par_cptn_env_comp:
  "(\<Gamma>,l) \<in> par_cptn \<and> Suc i<length l \<Longrightarrow> 
   \<Gamma>\<turnstile>\<^sub>p l!i \<rightarrow>\<^sub>e (l!(Suc i)) \<or> \<Gamma> \<turnstile>\<^sub>p l!i \<rightarrow> (l!(Suc i))"
proof -
  assume a0:"(\<Gamma>,l) \<in> par_cptn \<and> Suc i<length l"         
  then obtain c1 s1 c2 s2 where li:"l!i=(c1,s1) \<and> l!(Suc i) = (c2,s2)"  by fastforce
  obtain xs ys where l:"l= xs@((l!i)#(l!(Suc i))#ys)" using a0
    by (metis Cons_nth_drop_Suc Suc_less_SucD id_take_nth_drop less_SucI)
  moreover then have "(drop (length xs) l) = ((l!i)#(l!(Suc i))#ys)"
    by (metis append_eq_conv_conj) 
  moreover then have "length xs < length l" using leI by fastforce 
  ultimately have "(\<Gamma>,((l!i)#(l!(Suc i))#ys))\<in>par_cptn" 
    using a0 droppar_cptn_is_par_cptn by fastforce
  also then have "(\<Gamma>,(l!(Suc i))#ys)\<in>par_cptn" using par_cptn_dest li by fastforce
  ultimately show ?thesis using li par_cptn_elim_cases(2)
    by metis
qed


lemma three:
  "\<lbrakk>xs\<noteq>[]; \<forall>i<length xs. R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Guar (xs ! j)))
       \<subseteq> (Rely (xs ! i));
   p \<subseteq> (\<Inter>i<length xs. (Pre (xs ! i)));
   \<forall>i<length xs.
     \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Com (xs ! i) sat [Pre (xs!i), Rely (xs ! i), Guar (xs ! i), Post (xs ! i),Abr (xs ! i)];
   length xs=length clist; (\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s; (\<Gamma>,l) \<in> par_assum(p, R);
    \<forall>i<length clist. clist!i\<in>cp \<Gamma> (Com(xs!i)) s; (\<Gamma>,l) \<propto> clist; (\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]);
    snd (last l) \<notin> Fault ` F\<rbrakk>
  \<Longrightarrow> \<forall>j i. i<length clist \<and> Suc j<length l \<longrightarrow>  \<Gamma>\<turnstile>\<^sub>c((snd (clist!i))!j) \<rightarrow>\<^sub>e  ((snd (clist!i))!Suc j) \<longrightarrow>
      (snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in>            
             (R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Guar (xs ! j))))"
proof -
 assume a0:"xs\<noteq>[]" and
        a1:"\<forall>i<length xs. R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Guar (xs ! j)))
             \<subseteq> (Rely (xs ! i))" and
        a2: "p \<subseteq> (\<Inter>i<length xs.  (Pre (xs ! i)))" and
        a3: "\<forall>i<length xs.
               \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Com (xs ! i) sat [Pre (xs!i), Rely (xs ! i), Guar (xs ! i), Post (xs ! i),Abr (xs ! i)]" and
        a4: "length xs=length clist" and
        a5: "(\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s" and
        a6: "(\<Gamma>,l) \<in> par_assum(p, R)" and
        a7: "\<forall>i<length clist. clist!i\<in>cp \<Gamma> (Com(xs!i)) s" and
        a8: "(\<Gamma>,l) \<propto> clist" and
        a9: "(\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a])" and
        10: "snd (last l) \<notin> Fault ` F" 
  {
  fix j i ns ns'
  assume a00:"i<length clist \<and> Suc j<length l" and
         a11: "\<Gamma>\<turnstile>\<^sub>c((snd (clist!i))!j) \<rightarrow>\<^sub>e  ((snd (clist!i))!Suc j)"         
  then have two:"\<forall>j i ns ns'. i<length clist \<and> Suc j<length l \<longrightarrow> 
      \<Gamma>\<turnstile>\<^sub>c((snd (clist!i))!j) \<rightarrow>  ((snd (clist!i))!Suc j) \<longrightarrow>      
        (snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in> (Guar(xs!i))"
     using two[OF a1 a2 a3 a4 a5 a6 a7 a8 a9 10] by auto
  then have j_lenl:"Suc j<length l" using a00 by fastforce
  have i_lj:"i<length (fst (l!j)) \<and> i<length (fst (l!(Suc j)))" 
            using conjoin_same_length a00 a8 by fastforce 
  have fst_clist_\<Gamma>:"\<forall>i<length clist. fst(clist!i) = \<Gamma>" using a8 unfolding conjoin_def same_functions_def by fastforce
  have "(\<Gamma>\<turnstile>\<^sub>p(l!j)  \<rightarrow> (l!(Suc j))) \<and> 
            (\<exists>i<length clist. 
               ((fst (clist!i))\<turnstile>\<^sub>c ((snd (clist!i))!j)  \<rightarrow> ((snd (clist!i))!(Suc j))) \<and> 
            (\<forall>l<length clist. 
               l\<noteq>i \<longrightarrow>  (fst (clist!l))\<turnstile>\<^sub>c (snd (clist!l))!j  \<rightarrow>\<^sub>e ((snd (clist!l))!(Suc j)))) \<or> 
         (\<Gamma>\<turnstile>\<^sub>p(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)) \<and> 
          (\<forall>i<length clist.  (fst (clist!i))\<turnstile>\<^sub>c (snd (clist!i))!j  \<rightarrow>\<^sub>e ((snd (clist!i))!(Suc j))))"
  using a8 a00 unfolding conjoin_def compat_label_def by simp
  then have compat_label:"(\<Gamma>\<turnstile>\<^sub>p(l!j)  \<rightarrow> (l!(Suc j))) \<and> 
            (\<exists>i<length clist. 
               (\<Gamma>\<turnstile>\<^sub>c ((snd (clist!i))!j)  \<rightarrow> ((snd (clist!i))!(Suc j))) \<and> 
            (\<forall>l<length clist. 
               l\<noteq>i \<longrightarrow>  \<Gamma>\<turnstile>\<^sub>c (snd (clist!l))!j  \<rightarrow>\<^sub>e ((snd (clist!l))!(Suc j)))) \<or> 
         (\<Gamma>\<turnstile>\<^sub>p(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)) \<and> 
          (\<forall>i<length clist.  \<Gamma>\<turnstile>\<^sub>c (snd (clist!i))!j  \<rightarrow>\<^sub>e ((snd (clist!i))!(Suc j))))"
  using fst_clist_\<Gamma> by blast
  then have "(snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in>            
               (R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. Guar (xs ! j)))" 
  proof        
    assume a10:"(\<Gamma>\<turnstile>\<^sub>p(l!j)  \<rightarrow> (l!(Suc j))) \<and> 
            (\<exists>i<length clist. 
               (\<Gamma>\<turnstile>\<^sub>c ((snd (clist!i))!j)  \<rightarrow> ((snd (clist!i))!(Suc j))) \<and> 
            (\<forall>l<length clist. 
               l\<noteq>i \<longrightarrow>  \<Gamma>\<turnstile>\<^sub>c (snd (clist!l))!j  \<rightarrow>\<^sub>e ((snd (clist!l))!(Suc j))))" 
    then obtain i' where 
            a20:"i'<length clist \<and> 
             (\<Gamma>\<turnstile>\<^sub>c ((snd (clist!i'))!j)  \<rightarrow> ((snd (clist!i'))!(Suc j))) \<and> 
             (\<forall>l<length clist. 
                l\<noteq>i' \<longrightarrow>  \<Gamma>\<turnstile>\<^sub>c (snd (clist!l))!j  \<rightarrow>\<^sub>e ((snd (clist!l))!(Suc j)))" by blast    
    thus ?thesis 
    proof (cases "i'=i")
      case True note eq_i = this      
      then obtain P S1 S2 where P:"(snd (clist!i'))!j=(P,S1) \<and> ((snd (clist!i'))!(Suc j)) = (P,S2)"   
        using a11 by (fastforce elim:etranE)       
      thus ?thesis 
      proof (cases "S1 = S2")
        case True 
        have snd_lj:"(snd (l!j)) = snd ((snd (clist!i'))!j)"
            using a8 a20 a00 unfolding conjoin_def same_state_def
            by fastforce     
        have all_e:"(\<forall>l<length clist. \<Gamma>\<turnstile>\<^sub>c (snd (clist!l))!j  \<rightarrow>\<^sub>e ((snd (clist!l))!(Suc j)))"
          using a11 a20 eq_i by fastforce
        then have allP:"\<forall>l< length clist. fst ((snd (clist!l))!j) = fst ((snd (clist!l))!(Suc j))"
           by (fastforce elim:etranE)
        then have "fst (l!j) = (fst (l!(Suc j)))"
          using a8 conjoin_same_program_i_j [of "(\<Gamma>,l)"] a00 by fastforce
        also have "snd (l!j) = snd (l!(Suc j))"
        proof -              
          have "(snd (l!Suc j)) = snd ((snd (clist!i'))!(Suc j))"
            using a8 a20 a00 unfolding conjoin_def same_state_def
            by fastforce
          then show ?thesis using snd_lj P True by auto
        qed 
        ultimately have "l!j = l!(Suc j)" by (simp add: prod_eq_iff) 
        moreover have ns1:"\<exists>ns1. S1=Normal ns1" 
          using P a20 step_change_p_or_eq_s by fastforce                    
        ultimately have "\<Gamma>\<turnstile>\<^sub>p(l!j)  \<rightarrow>\<^sub>e (l!(Suc j))" 
          using P step_pe.ParEnv snd_lj by (metis prod.collapse snd_conv)          
        then have "(snd (l ! j), snd (l ! Suc j)) \<in> R "
          using a00 a6 unfolding par_assum_def by fastforce
        then show ?thesis using a8 a00 
          unfolding conjoin_def same_state_def  
         by fastforce
      next
        case False thus ?thesis 
          using a20 P a11 step_change_p_or_eq_s by fastforce
      qed
    next
      case False 
      have i'_clist:"i' < length clist" using a20 by fastforce
      then have clist_i'_Guardxs:"(snd((snd (clist!i'))!j), snd((snd (clist!i'))!Suc j)) \<in> Guar(xs!i')"
        using two a00 False a8 unfolding conjoin_def same_state_def
        by (metis a20)
      have "snd((snd (clist!i))!j) = snd (l!j) \<and> snd((snd (clist!i))!Suc j) = snd (l!Suc j)" 
        using a00 a20 a8 unfolding conjoin_def same_state_def by fastforce
      also have "snd((snd (clist!i'))!j) = snd (l!j) \<and> snd((snd (clist!i'))!Suc j) = snd (l!Suc j)"
        using j_lenl a20 a8 unfolding conjoin_def same_state_def by fastforce
      ultimately have "snd((snd (clist!i))!j) = snd((snd (clist!i'))!j) \<and> 
                    snd((snd (clist!i))!Suc j) = snd((snd (clist!i'))!Suc j)" 
      by fastforce
      then have clist_i_Guardxs:
        "(snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in> 
            Guar(xs!i')"  
      using  clist_i'_Guardxs by fastforce      
      thus ?thesis  
        using False a20  a4 by fastforce        
    qed
  next
    assume a10:"(\<Gamma>\<turnstile>\<^sub>p(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)) \<and> 
          (\<forall>i<length clist.  \<Gamma>\<turnstile>\<^sub>c (snd (clist!i))!j  \<rightarrow>\<^sub>e ((snd (clist!i))!(Suc j))))"      
    then have "(snd (l ! j), snd (l ! Suc j)) \<in> R"
      using a00 a10 a6 unfolding par_assum_def by fastforce
    then show ?thesis using a8 a00 
      unfolding conjoin_def same_state_def
      by fastforce
  qed
  }  thus ?thesis by blast
qed

definition tran_True where "tran_True \<equiv> True"

definition after where "after \<equiv> True"

lemma four:
  "\<lbrakk>xs\<noteq>[];  \<forall>i<length xs.  R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Guar (xs ! j)))
       \<subseteq>  (Rely (xs ! i));
   (\<Union>j<length xs.  (Guar (xs ! j))) \<subseteq> (G);
   p \<subseteq> (\<Inter>i<length xs.  (Pre (xs ! i)));
   \<forall>i<length xs.
     \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Com (xs ! i) sat [Pre (xs!i),  Rely (xs ! i), Guar (xs ! i), Post (xs ! i),Abr (xs ! i)];
    (\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s; (\<Gamma>,l) \<in> par_assum(p, R); Suc i < length l;
   \<Gamma>\<turnstile>\<^sub>p (l!i) \<rightarrow> (l!(Suc i));
   (\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]);
   snd (last l) \<notin> Fault ` F\<rbrakk>
  \<Longrightarrow> (snd (l ! i), snd (l ! Suc i)) \<in> G"
proof -
  assume a0:"xs\<noteq>[]" and
         a1:"\<forall>i<length xs.  R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Guar (xs ! j)))
             \<subseteq>  (Rely (xs ! i))" and
         a2:"(\<Union>j<length xs.  (Guar (xs ! j))) \<subseteq> (G)" and
         a3:"p \<subseteq> (\<Inter>i<length xs.  (Pre (xs ! i)))" and
         a4:"\<forall>i<length xs.
           \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Com (xs ! i) sat [Pre (xs!i),  Rely (xs ! i), Guar (xs ! i), Post (xs ! i),Abr (xs ! i)]" and
         a5:"(\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s" and
         a6:"(\<Gamma>,l) \<in> par_assum(p, R)" and
         a7: "Suc i < length l" and
         a8:"\<Gamma>\<turnstile>\<^sub>p (l!i) \<rightarrow> (l!(Suc i))" and         
         a10:"(\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a])" and
         a11:"snd (last l) \<notin> Fault ` F"
   have length_par_xs:"length (ParallelCom xs) = length xs" unfolding ParallelCom_def  by fastforce   
   then have "(ParallelCom xs)\<noteq>[]" using a0 by fastforce 
   then have "(\<Gamma>,l) \<in>{(\<Gamma>1,c). \<exists>clist. (length clist)=(length (ParallelCom xs)) \<and> 
               (\<forall>i<length clist. (clist!i) \<in> cp \<Gamma> ((ParallelCom xs)!i) s) \<and> (\<Gamma>,c) \<propto> clist \<and> \<Gamma>1=\<Gamma>}"
     using one a5 by fastforce
   then obtain clist where "(length clist)=(length xs) \<and> 
               (\<forall>i<length clist. (clist!i) \<in> cp \<Gamma> ((ParallelCom xs)!i) s) \<and> (\<Gamma>,l) \<propto> clist"
     using length_par_xs by auto
   then have conjoin:"(length clist)=(length xs) \<and> 
               (\<forall>i<length clist. (clist!i) \<in> cp \<Gamma>  (Com (xs ! i)) s) \<and> (\<Gamma>,l) \<propto> clist"
     using ParallelCom_Com by fastforce
   then have length_xs_clist:"length xs = length clist" by auto 
   have clist_cp:"\<forall>i<length clist. (clist!i) \<in> cp \<Gamma>  (Com (xs ! i)) s" using conjoin by auto
   have conjoin:"(\<Gamma>,l) \<propto> clist" using conjoin by auto     
   have l_not_empty:"l\<noteq>[]" using a5 par_cptn.simps unfolding par_cp_def by fastforce
   then have l_g0:"0<length l" by fastforce  
   then have last_l:"last l = l!((length l) - 1)" by (simp add: last_conv_nth)    
   have "\<forall>i< length l. fst (l!i) = map (\<lambda>x. fst ((snd x)!i)) clist"
     using conjoin unfolding conjoin_def same_program_def by fastforce
   obtain Ps si Ps' ssi where li:"l!i = (Ps,si) \<and> l!(Suc i) = (Ps', ssi)" by fastforce
   then have "\<exists>j r. j<length Ps \<and> Ps' = Ps[j:=r] \<and> (\<Gamma>\<turnstile>\<^sub>c((Ps!j),si) \<rightarrow> (r, ssi))" 
     using a8 par_ctranE by fastforce
   then obtain j r where step_c:"j<length Ps \<and> Ps' = Ps[j:=r] \<and> (\<Gamma>\<turnstile>\<^sub>c((Ps!j),si) \<rightarrow> (r, ssi))"
     by auto   
   have length_Ps_clist:
     "length Ps = length clist \<and> length Ps = length Ps'" 
     using conjoin a7 conjoin_same_length li step_c by fastforce
   have from_step:"(snd (clist!j))!i = ((Ps!j),si) \<and> (snd (clist!j))!(Suc i) = (Ps'!j,ssi)"  
   proof -     
     have f2: "Ps = fst (snd (\<Gamma>, l) ! i)" and f2':"Ps' = fst (snd (\<Gamma>, l) ! (Suc i))"
       using li by auto
     have f3:"si = snd (snd (\<Gamma>, l) ! i) \<and> ssi = snd (snd (\<Gamma>, l) ! (Suc i))"
       by (simp add: li)
     then have "(snd (clist!j))!i = ((Ps!j),si)"
       using f2 conjoin a7 step_c unfolding conjoin_def same_program_def same_state_def by force     
     moreover have "(snd (clist!j))!(Suc i) = (Ps'!j,ssi)"
       using f2' f3 conjoin a7 step_c length_Ps_clist 
      unfolding conjoin_def same_program_def same_state_def 
       by auto
     ultimately show ?thesis by auto
   qed      
   then have step_clist:"\<Gamma>\<turnstile>\<^sub>c(snd (clist!j))!i \<rightarrow> (snd (clist!j))!(Suc i)" 
     using from_step  step_c by fastforce
   have j_xs:"j<length xs" using step_c length_Ps_clist length_xs_clist by auto
   have "j<length clist" using j_xs length_xs_clist by auto    
   also have 
     "\<forall>i j ns ns'. j < length clist \<and> Suc i < length l \<longrightarrow>
            \<Gamma>\<turnstile>\<^sub>c snd (clist ! j) ! i \<rightarrow> snd (clist ! j) ! Suc i \<longrightarrow>             
              (snd (snd (clist ! j) ! i), snd (snd (clist ! j) ! Suc i)) \<in> Guar (xs ! j)"
    using two[OF a1 a3 a4 length_xs_clist a5 a6 clist_cp conjoin a10 a11] by auto
   ultimately have "(snd (snd (clist ! j) ! i), snd (snd (clist ! j) ! Suc i)) \<in> Guar (xs ! j)"
     using a7 step_c length_Ps_clist step_clist by metis     
   then have "(snd (l!i), snd (l!(Suc i)))\<in> Guar (xs ! j)"
      using from_step a2 length_xs_clist step_c li by fastforce
   then show ?thesis using a2 j_xs
     unfolding sep_conj_def tran_True_def after_def Satis_def by fastforce
qed

lemma same_program_last:"l\<noteq>[] \<Longrightarrow> (\<Gamma>,l) \<propto> clist  \<Longrightarrow> i<length clist \<Longrightarrow>fst (last (snd (clist!i))) = fst (last l) ! i" 
proof -
   assume l_not_empty:"l\<noteq>[]" and
          conjoin: "(\<Gamma>,l) \<propto> clist" and
          i_clist: "i<length clist"
   have last_clist_eq_l:"\<forall>i<length clist. last (snd (clist!i)) = (snd (clist!i))!((length l) - 1)"
          using conjoin  last_conv_nth l_not_empty 
          unfolding conjoin_def same_length_def
          by (metis length_0_conv snd_eqD) 
   then have last_l:"last l = l!((length l)-1)" using l_not_empty by (simp add: last_conv_nth)
   have "fst (last l) = map (\<lambda>x. fst (snd x ! ((length l)-1))) clist"
     using l_not_empty last_l conjoin unfolding conjoin_def same_program_def  by auto
   also have "(map (\<lambda>x. fst (snd x ! ((length l)-1))) clist)!i = 
            fst ((snd (clist!i))! ((length l)-1))" using i_clist by fastforce
   also have  "fst ((snd (clist!i))! ((length l)-1)) = 
             fst ((snd (clist!i))! ((length (snd (clist!i)))-1))" 
     using conjoin i_clist unfolding conjoin_def same_length_def by fastforce
   also then have "fst ((snd (clist!i))! ((length (snd (clist!i)))-1)) = fst (last (snd (clist!i)))"
     using i_clist l_not_empty conjoin last_clist_eq_l last_conv_nth unfolding conjoin_def same_length_def
     by presburger
   finally show ?thesis by auto
qed



lemma five:
  "\<lbrakk>xs\<noteq>[];  \<forall>i<length xs.  R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Guar (xs ! j)))
       \<subseteq> (Rely (xs ! i));
   p \<subseteq> (\<Inter>i<length xs. (Pre (xs ! i)));
   (\<Inter>i<length xs. (Post (xs ! i))) \<subseteq> q;
   (\<Union>i<length xs. (Abr (xs ! i))) \<subseteq> a ;
   \<forall>i < length xs.
    \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Com (xs ! i) sat [Pre (xs!i), Rely (xs ! i), Guar (xs ! i), Post (xs ! i),Abr (xs ! i)];
    (\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s; (\<Gamma>,l) \<in> par_assum(p, R);
   All_End (last l); snd (last l) \<notin> Fault ` F;(\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]) \<rbrakk> \<Longrightarrow> 
                   (\<exists>j<length (fst (last l)). fst (last l)!j=Throw \<and> 
                        snd (last l) \<in> Normal ` (a)) \<or>
                   (\<forall>j<length (fst (last l)). fst (last l)!j=Skip \<and>
                        snd (last l) \<in> Normal ` q)"
proof-
  assume a0:"xs\<noteq>[]" and 
         a1:"\<forall>i<length xs.  R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Guar (xs ! j)))
                                                                     \<subseteq>  (Rely (xs ! i))" and
         a2:"p \<subseteq> (\<Inter>i<length xs. (Pre (xs ! i)))" and
         a3:"(\<Inter>i<length xs. (Post (xs ! i))) \<subseteq> q" and
         a4:"(\<Union>i<length xs. (Abr (xs ! i))) \<subseteq> a" and
         a5:"\<forall>i < length xs.
               \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Com (xs ! i) sat [Pre (xs!i), 
                                             Rely (xs ! i), Guar (xs ! i), 
                                             Post (xs ! i),Abr (xs ! i)]" and
         a6:"(\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s" and
         a7:"(\<Gamma>,l) \<in> par_assum(p, R)"and
         a8:"All_End (last l)" and
         a9:"snd (last l) \<notin> Fault ` F" and
         a10:"(\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a])"
   have length_par_xs:"length (ParallelCom xs) = length xs" unfolding ParallelCom_def  by fastforce   
   then have "(ParallelCom xs)\<noteq>[]" using a0 by fastforce
   then have "(\<Gamma>,l) \<in>{(\<Gamma>1,c). \<exists>clist. (length clist)=(length (ParallelCom xs)) \<and> 
               (\<forall>i<length clist. (clist!i) \<in> cp \<Gamma> ((ParallelCom xs)!i) s) \<and> (\<Gamma>,c) \<propto> clist \<and> \<Gamma>1=\<Gamma>}"
     using one a6 by fastforce
   then obtain clist where "(length clist)=(length xs) \<and> 
               (\<forall>i<length clist. (clist!i) \<in> cp \<Gamma> ((ParallelCom xs)!i) s) \<and> (\<Gamma>,l) \<propto> clist"
     using length_par_xs by auto
   then have conjoin:"(length clist)=(length xs) \<and> 
               (\<forall>i<length clist. (clist!i) \<in> cp \<Gamma>  (Com (xs ! i)) s) \<and> (\<Gamma>,l) \<propto> clist"
     using ParallelCom_Com by fastforce
   then have length_xs_clist:"length xs = length clist" by auto
   (*have length_l_clist: "length l = length clist" 
     using conjoin unfolding conjoin_def same_length_def *)
   have clist_cp:"\<forall>i<length clist. (clist!i) \<in> cp \<Gamma>  (Com (xs ! i)) s" using conjoin by auto
   have conjoin:"(\<Gamma>,l) \<propto> clist" using conjoin by auto
   have l_not_empty:"l\<noteq>[]" using a6 par_cptn.simps unfolding par_cp_def by fastforce
   then have l_g0:"0<length l" by fastforce  
   then have last_l:"last l = l!((length l) - 1)" by (simp add: last_conv_nth) 
   have clist_assum:"\<forall>i<length clist. (clist!i) \<in> assum (Pre (xs!i),Rely (xs!i))"     
   proof -
   { fix i
     assume i_length:"i<length clist"
     obtain \<Gamma>1 li where clist:"clist!i=(\<Gamma>1,li)" by fastforce    
     then have \<Gamma>eq:"\<Gamma>1=\<Gamma>" 
       using conjoin i_length unfolding conjoin_def same_functions_def by fastforce
     have "(\<Gamma>1,li) \<in> assum (Pre (xs!i),Rely (xs!i))"
     proof-
       have l:"snd (li!0) \<in> Normal ` ( (Pre (xs!i)))"
       proof -  
         have snd_l:"snd (\<Gamma>,l) = l" by fastforce       
         have "snd (l!0) \<in> Normal ` (p)" 
         using a7 unfolding par_assum_def by fastforce         
         also have "snd (l!0) = snd (li!0)"           
           using i_length conjoin l_g0 clist 
           unfolding conjoin_def same_state_def by fastforce
         finally show ?thesis using a2 i_length length_xs_clist
            by auto 
       qed              
       have r:"(\<forall>j. Suc j < length li \<longrightarrow> 
                    \<Gamma>\<turnstile>\<^sub>c(li!j)  \<rightarrow>\<^sub>e (li!(Suc j)) \<longrightarrow>                 
                    (snd(li!j), snd(li!(Suc j))) \<in> Rely (xs!i))"        
         using three[OF a0 a1 a2 a5 length_xs_clist a6 a7 clist_cp conjoin a10 a9]  
               i_length conjoin a1 length_xs_clist clist                     
         unfolding assum_def conjoin_def same_length_def by fastforce                                   
       show ?thesis using l r \<Gamma>eq unfolding assum_def by fastforce
     qed 
     then have "clist!i \<in> assum (Pre (xs!i),Rely (xs!i))" using clist by auto            
   } thus ?thesis by auto
   qed
   then have clist_com:"\<forall>i<length clist. (clist!i) \<in> comm  (Guar (xs!i),(Post(xs!i),Abr (xs!i))) F"
     using a5 unfolding com_cvalidity_def 
     using a10 unfolding com_validity_def using clist_cp length_xs_clist
     by force              
   have last_clist_eq_l:"\<forall>i<length clist. last (snd (clist!i)) = (snd (clist!i))!((length l) - 1)"
     using conjoin  last_conv_nth l_not_empty 
     unfolding conjoin_def same_length_def
     by (metis length_0_conv snd_eqD) 
   then have last_clist_l:"\<forall>i<length clist. snd (last (snd (clist!i))) = snd (last l)"
     using last_l conjoin l_not_empty unfolding conjoin_def same_state_def same_length_def 
     by simp
   show ?thesis
   proof(cases "\<forall>i<length (fst (last l)). fst (last l)!i = Skip")
     assume ac1:"\<forall>i<length (fst (last l)). fst (last l)!i = Skip"
     have "(\<forall>j<length (fst (last l)). fst (last l) ! j = LanguageCon.com.Skip \<and> snd (last l) \<in> Normal ` q)"
     proof -
       {fix j
        assume aj:"j<length (fst (last l))"         
        have "\<forall>i<length clist. snd (last (snd (clist!i))) \<in> Normal ` Post(xs!i)"
        proof-
          {fix i 
           assume a20:"i<length clist"
           then have snd_last:"snd (last (snd (clist!i))) = snd (last l)" 
             using last_clist_l by fastforce
           have last_clist_not_F:"snd (last (snd (clist!i)))\<notin> Fault ` F"
              using a9 last_clist_l a20 by fastforce
           have "fst (last l) ! i = Skip" 
             using a20 ac1 conjoin_same_length[OF conjoin]
             by (simp add: l_not_empty last_l )                       
           also have "fst (last l) ! i=fst (last (snd (clist!i)))"
             using same_program_last[OF l_not_empty conjoin a20]  by auto
           finally have "fst (last (snd (clist!i))) = Skip" .
           then have "snd (last (snd (clist!i))) \<in> Normal ` Post(xs!i)" 
             using clist_com last_clist_not_F a20
             unfolding comm_def final_def by fastforce
          }  thus ?thesis by auto 
        qed             
        then have "\<forall>i<length xs. snd (last l) \<in> Normal ` Post(xs!i)" 
          using last_clist_l length_xs_clist by fastforce
        then have "\<forall>i<length xs. \<exists>x\<in>( Post(xs!i)). snd (last l) = Normal x"
          by fastforce
        moreover have "\<forall>t. (\<forall>i<length xs. t\<in> Post (xs ! i))\<longrightarrow> t\<in> q" using a3
          by fastforce        
        ultimately have "(\<exists>x\<in> q. snd (last l) = Normal x)" using a0
           by (metis (mono_tags, lifting) length_greater_0_conv xstate.inject(1)) 
        then have "snd (last l) \<in> Normal ` q" by fastforce          
        then have "fst (last l) ! j = LanguageCon.com.Skip \<and> snd (last l) \<in> Normal ` q"
          using aj ac1 by fastforce
        } thus ?thesis by auto
     qed      
     thus ?thesis by auto
   next
     assume "\<not> (\<forall>i<length (fst (last l)). fst (last l)!i = Skip)"    
     then obtain i where a20:"i< length (fst (last l)) \<and>  fst (last l)!i \<noteq> Skip" 
       by fastforce
     then have last_i_throw:"fst (last l)!i = Throw \<and> (\<exists>n. snd (last l) = Normal n)" 
       using a8 unfolding All_End_def final_def by fastforce     
     have "length (fst (last l)) =  length clist" 
       using conjoin_same_length[OF conjoin] l_not_empty last_l
       by simp
     then have i_length:"i<length clist" using a20 by fastforce
     then have snd_last:"snd (last (snd (clist!i))) = snd (last l)" 
       using last_clist_l by fastforce
     have last_clist_not_F:"snd (last (snd (clist!i)))\<notin> Fault ` F"
       using a9 last_clist_l i_length by fastforce
     then have "fst (last (snd (clist!i))) = fst (last l) ! i" 
       using i_length same_program_last [OF l_not_empty conjoin] by fastforce
     then have "fst (last (snd (clist!i))) = Throw"
       using last_i_throw by fastforce
     then have "snd (last (snd (clist!i))) \<in> Normal `  Abr(xs!i)" 
       using clist_com last_clist_not_F i_length last_i_throw snd_last
       unfolding comm_def final_def by fastforce
     then have "snd (last l)\<in> Normal ` Abr(xs!i)" using last_clist_l i_length
       by fastforce
     then have "snd (last l)\<in> Normal ` (a)" using a4 a0 i_length length_xs_clist by fastforce
     then have "\<exists>j<length (fst (last l)).
        fst (last l) ! j = LanguageCon.com.Throw \<and> snd (last l) \<in> Normal ` a"
     using last_i_throw a20 by fastforce
     thus ?thesis by auto
   qed 
qed


lemma ParallelEmpty [rule_format]:
  "\<forall>i s. (\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom []) s \<longrightarrow>
  Suc i < length l \<longrightarrow> \<not> (\<Gamma> \<turnstile>\<^sub>p (l!i) \<rightarrow> (l!Suc i))"
apply(induct_tac l)
 apply simp
apply clarify
apply(case_tac list,simp,simp)
apply(case_tac i)
 apply(simp add:par_cp_def ParallelCom_def) 
 apply(erule par_ctranE,simp)
apply(simp add:par_cp_def ParallelCom_def)
apply clarify
apply(erule par_cptn.cases,simp)
 apply simp
by (metis list.inject list.size(3) not_less0 step_p_pair_elim_cases)

lemma ParallelEmpty2:
  assumes a0:"(\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom []) s" and
         a1: "i < length l" 
  shows "fst (l!i) = []"
proof -
  have paremp:"ParallelCom [] = []" unfolding ParallelCom_def by auto
  then have l0:"l!0 =([],s)" using a0 unfolding par_cp_def by auto
  then have "(\<Gamma>,l) \<in> par_cptn" using a0 unfolding par_cp_def by fastforce
  thus ?thesis using l0 a1
  proof (induct arbitrary: i s) 
    case ParCptnOne thus ?case by auto
  next
    case (ParCptnEnv \<Gamma> P s1 t xs i s)
    thus ?case
    proof -
      have f1: "i < Suc (Suc (length xs))"
        using ParCptnEnv.prems(2) by auto
      have "(P, s1) = ([], s)"
        using ParCptnEnv.prems(1) by auto
      then show ?thesis
        using f1 by (metis (no_types) ParCptnEnv.hyps(3) diff_Suc_1 fst_conv length_Cons less_Suc_eq_0_disj nth_Cons')
    qed    
  next
    case (ParCptnComp \<Gamma> P s1 Q t xs)   
    have "(\<Gamma>, (P,s1)#(Q, t) # xs) \<in> par_cp \<Gamma> (ParallelCom []) s1" 
        using ParCptnComp(4) ParCptnComp(1) step_p_elim_cases by fastforce
    then have "\<not> \<Gamma>\<turnstile>\<^sub>p (P, s1) \<rightarrow> (Q, t)" using ParallelEmpty ParCptnComp by fastforce
    thus ?case using ParCptnComp by auto
  qed
qed  

lemma parallel_sound: 
  "\<forall>i<length xs.
       R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Guar (xs ! j)))
       \<subseteq> (Rely (xs ! i)) \<Longrightarrow>
    (\<Union>j<length xs. (Guar (xs ! j))) \<subseteq> G \<Longrightarrow>
    p \<subseteq> (\<Inter>i<length xs. (Pre (xs ! i))) \<Longrightarrow>
    (\<Inter>i<length xs. (Post (xs ! i))) \<subseteq> q \<Longrightarrow>
    (\<Union>i<length xs. (Abr (xs ! i))) \<subseteq> a \<Longrightarrow>    
    \<forall>i<length xs.
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Com (xs !i) sat [Pre (xs !i), Rely (xs ! i), Guar (xs ! i), Post (xs ! i),Abr (xs ! i)] \<Longrightarrow>
  \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> ParallelCom xs SAT [p, R, G, q,a]
  "
proof -
  assume 
  a0:"\<forall>i<length xs.
      R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Guar (xs ! j)))
       \<subseteq>  (Rely (xs ! i))" and
   a1:"(\<Union>j<length xs.  (Guar (xs ! j))) \<subseteq> G" and
   a2:"p \<subseteq> (\<Inter>i<length xs.  (Pre (xs ! i)))" and
   a3:"(\<Inter>i<length xs.  (Post (xs ! i))) \<subseteq> q" and
   a4:"(\<Union>i<length xs.  (Abr (xs ! i))) \<subseteq> a" and
   a5:"\<forall>i<length xs.
            \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Com (xs !i) sat [Pre (xs !i), Rely (xs ! i), Guar (xs ! i), Post (xs ! i),Abr (xs ! i)]"
  { 
     assume a00:"(\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a])"
     { fix s l
       assume a10: "(\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s \<and> (\<Gamma>,l) \<in> par_assum(p, R)"       
       then have c_par_cp:"(\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s" by auto
       have c_par_assum: "(\<Gamma>,l) \<in> par_assum(p, R)" using a10 by auto
       { fix i ns ns'
         assume a20:"snd (last l) \<notin> Fault ` F"
         {
            assume a30:"Suc i<length l"  and
                   a31: "\<Gamma>\<turnstile>\<^sub>p(l!i)  \<rightarrow> (l!(Suc i))"                   
            have xs_not_empty:"xs\<noteq>[]" 
            proof -
            {
              assume "xs = []"
              then have "\<not> (\<Gamma> \<turnstile>\<^sub>p (l!i) \<rightarrow> (l!Suc i))" 
                using a30 a10 ParallelEmpty by fastforce
              then have False using a31 by auto
            } thus ?thesis by auto
            qed            
            then have "(snd(l!i), snd(l!(Suc i))) \<in>  G"
            using four[OF xs_not_empty a0 a1 a2 a5 c_par_cp c_par_assum a30 a31 a00 a20] by blast
            
         } then have "Suc i<length l \<longrightarrow> 
                     \<Gamma>\<turnstile>\<^sub>p(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow>                      
                     (snd(l!i), snd(l!(Suc i))) \<in> G " by auto 
            note l = this
         { assume a30:"All_End (last l)"
           then have xs_not_empty:"xs\<noteq>[]" 
           proof - 
           { assume xs_emp:"xs=[]"
             have lenl:"0<length l" using a10 unfolding par_cp_def using par_cptn.simps by fastforce
             then have "(length l) - 1 < length l" by fastforce
             then have "fst(l!((length l) - 1)) = []" using ParallelEmpty2 a10 xs_emp by fastforce
             then have False using a30 lenl unfolding All_End_def
               by (simp add: last_conv_nth )              
           } thus ?thesis by auto
           qed
           then have "(\<exists>j<length (fst (last l)). fst (last l)!j=Throw \<and> 
                        snd (last l) \<in> Normal ` (a)) \<or>
                      (\<forall>j<length (fst (last l)). fst (last l)!j=Skip \<and>
                        snd (last l) \<in> Normal ` q)"
           using five[OF xs_not_empty a0 a2 a3 a4 a5 c_par_cp c_par_assum a30 a20 a00] by blast
         } then have "All_End (last l) \<longrightarrow> 
                      (\<exists>j<length (fst (last l)). fst (last l)!j=Throw \<and> 
                        snd (last l) \<in> Normal ` (a)) \<or>
                   (\<forall>j<length (fst (last l)). fst (last l)!j=Skip \<and>
                        snd (last l) \<in> Normal ` q)" by auto 
           note res1 = conjI[OF l this] 
       }
       then have  "(\<Gamma>,l) \<in> par_comm(G, (q,a)) F" unfolding par_comm_def by auto       
     } 
     then have "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (ParallelCom xs) SAT [p, R, G, q,a]" 
       unfolding par_com_validity_def par_cp_def by fastforce
  } thus ?thesis using par_com_cvalidity_def by fastforce
qed


theorem  
 par_rgsound:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> Ps SAT [p, R, G, q,a] \<Longrightarrow>
  \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> (ParallelCom Ps) SAT [p, R, G, q,a]"
proof (induction rule:par_rghoare.induct)
  case (Parallel xs R G p q a \<Gamma> \<Theta> F)
    thus ?case using localRG_sound com_cnvalid_to_cvalid parallel_sound[of xs R G p q a \<Gamma> \<Theta> F] 
      by fast
qed
lemma Conseq':"\<forall>s. s\<in>p \<longrightarrow>
              (\<exists>p' q' a' R' G'. 
                (\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [(p' Z), (R' Z), (G' Z), (q' Z),(a' Z)]) \<and>
                   (\<exists> Z. s\<in>p' Z \<and> (q' Z \<subseteq> q) \<and> (a' Z \<subseteq> a) \<and> (G' Z \<subseteq> G) \<and> (R \<subseteq> R' Z)))
              \<Longrightarrow>
              \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q,a]"
  apply (rule Conseq)
  by (meson order_refl)

lemma conseq:"\<lbrakk>\<forall>Z. \<Gamma>,\<Theta>'\<turnstile>\<^bsub>/F\<^esub> P sat [(p' Z), (R' Z), (G' Z), (q' Z),(a' Z)]; \<Theta>' \<subseteq> \<Theta> ;
              \<forall>s. s \<in> p \<longrightarrow> (\<exists> Z. s\<in>p' Z \<and> (q' Z \<subseteq> q) \<and> (a' Z \<subseteq> a) \<and> (G' Z \<subseteq> G) \<and> (R \<subseteq> R' Z))\<rbrakk>
              \<Longrightarrow>
               \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q,a]"
by (rule Conseq) (meson order_refl)

lemma conseqPrePost[trans]:
 "\<Gamma>,\<Theta>'\<turnstile>\<^bsub>/F\<^esub> P sat [p', R', G', q',a'] \<Longrightarrow> \<Theta>' \<subseteq> \<Theta> \<Longrightarrow>
  p\<subseteq>p' \<Longrightarrow> q' \<subseteq> q \<Longrightarrow> a' \<subseteq> a \<Longrightarrow> G' \<subseteq> G \<Longrightarrow> R \<subseteq> R' \<Longrightarrow> 
  \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q,a]"  
by (rule conseq) auto

lemma conseqPre[trans]:
 "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p', R, G, q,a] \<Longrightarrow>
  p\<subseteq>p' \<Longrightarrow>
  \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q,a]"
by (rule conseq) auto

lemma conseqPost[trans]:
 "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q',a'] \<Longrightarrow>
  q'\<subseteq>q \<Longrightarrow>  a'\<subseteq>a \<Longrightarrow>
  \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q,a]"
  by (rule conseq) auto
  
lemma shows x:"\<exists>(sa'::nat set). (\<forall>x. (x\<in> sa) = ((to_nat x) \<in> sa'))"
  by (metis (mono_tags, hide_lams) from_nat_to_nat imageE image_eqI)


lemma not_empty_set_countable: 
  assumes a0:"sa\<noteq>({}::('a::countable) set)" 
  shows "{i. ((\<lambda>i. i\<in> sa) o from_nat) i}\<noteq>{}"
  by (metis (full_types) Collect_empty_eq_bot assms comp_apply empty_def equals0I from_nat_to_nat)

lemma eq_set_countable:"(\<Inter>i\<in>{i. ((\<lambda>i. i\<in> sa) o from_nat) i}. (q o from_nat) i) = ((\<Inter>i\<in>sa. q i))"     
  apply auto
  by (metis (no_types) from_nat_to_nat)
  
lemma conj_inter_countable[trans]: 
  assumes a0:"sa\<noteq>({}::('a::countable) set)" and
          a1:"\<forall>i\<in>sa. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q i,a]"
  shows"\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G,(\<Inter>i\<in>sa. q i),a]"  
proof-
  have "\<forall>i\<in>{i. ((\<lambda>i. i\<in> sa) o from_nat) i}. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G,(q o from_nat) i,a]"    
    using a1 by auto
  then have "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G,\<Inter>i\<in>{i. ((\<lambda>i. i\<in> sa) o from_nat) i}. (q o from_nat) i,a]"
    using Conj_Inter[OF not_empty_set_countable[OF a0]]   by auto    
  thus ?thesis  using eq_set_countable
    by metis    
qed
  
lemma all_Post[trans]:
  assumes a0:"\<forall>p_n::('a::countable). \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [P, R, G, Q p_n, Qa]" 
  shows"\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [P, R, G,{s. \<forall>p_n. s\<in>Q p_n},Qa]"      
proof-  
  have "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [P, R, G,(\<Inter>p_n. Q  p_n),Qa]"
     using a0 conj_inter_countable[of UNIV]  by auto 
  moreover have s1:"\<forall>P. {s. \<forall>p_n. s\<in>P p_n} = (\<Inter>p_n. P p_n)"
    by auto   
  ultimately show ?thesis
   by (simp add: s1)
qed    
  
lemma all_Pre[trans]:
  assumes a0:"\<forall>p_n. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [P p_n, R, G, Q, Qa]" 
  shows"\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [{s. \<forall>p_n. s\<in>P p_n}, R, G,Q,Qa]"
proof-
   {fix p_n     
    have "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [{s. \<forall>p_n. s\<in>P p_n}, R, G,Q,Qa]" 
    proof-
      have "{v. \<forall>n. v \<in> P n} \<subseteq> P p_n" by force
      then show ?thesis by (meson a0 LocalRG_HoareDef.conseqPrePost subset_eq)
    qed
  } thus ?thesis by auto 
qed
    
lemma Pre_Post_all:
  assumes a0:"\<forall>p_n::('a::countable). \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [P p_n, R, G, Q p_n, Qa]" 
  shows"\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [{s. \<forall>p_n. s\<in>P p_n}, R, G,{s. \<forall>p_n. s\<in>Q p_n},Qa]"    
proof-
  {fix p_n
     
    have "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [{s. \<forall>p_n. s\<in>P p_n}, R, G,Q p_n,Qa]" 
    proof-
      have "{v. \<forall>n. v \<in> P n} \<subseteq> P p_n" by force
      then show ?thesis by (meson a0 LocalRG_HoareDef.conseqPrePost subset_eq)
    qed
  }
  then have f3:"\<forall>p_n. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [{s. \<forall>p_n. s\<in>P p_n}, R, G,Q p_n,Qa]"
    by auto
  then have "\<forall>p_n. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [{s. \<forall>p_n. s\<in>P p_n}, R, G,{s. \<forall>p_n. s\<in>Q p_n},Qa]"    
    using all_Post by auto
  moreover have s1:"\<forall>P. {s. \<forall>p_n. s\<in>P p_n} = (\<Inter>p_n. P p_n)"
    by auto   
  ultimately show ?thesis
   by (simp add: s1)
qed  
  
  
inductive_cases hoare_elim_skip_cases [cases set]:
"\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> Skip sat [p, R, G, q,a]"



(* abbreviation 
 "stepc_rtrancl" :: "[('s,'p,'f,'e) body,('s,'p,'f) config,('s,'p,'f) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sup>*/ _)" [81,81,81] 100)
 where                                
  "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sup>* cf1 \<equiv> ((CONST stepc \<Gamma>))\<^sup>*\<^sup>* cf0 cf1" *)


end


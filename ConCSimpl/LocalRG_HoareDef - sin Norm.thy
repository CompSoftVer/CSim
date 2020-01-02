theory LocalRG_HoareDef                       
imports "SmallStepCon" "../EmbSimpl/HoarePartialProps" 
begin
section \<open>Validity  of Correctness Formulas\<close>

subsection \<open>Aux\<close>
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
type_synonym ('s,'p,'f) rgformula =  
   "(('s,'p,'f) com \<times>      (* c *)
    ('s set) \<times>     (* P *)    
    (('s,'f) tran) set \<times> (* R *)
    (('s,'f) tran) set \<times> (* G *)
    ('s set) \<times> (* Q *)
    ('s set))" (* A *)
    
type_synonym ('s,'p,'f) sextuple =  
   "('p \<times>      (* c *)
    ('s set) \<times>     (* P *)    
    (('s,'f) tran) set \<times> (* R *)
    (('s,'f) tran) set \<times> (* G *)
    ('s set) \<times> (* Q *)
    ('s set))" (* A *)    

definition Sta :: "'s set \<Rightarrow> (('s,'f) tran) set \<Rightarrow> bool" where
  "Sta \<equiv> \<lambda>f g. (\<forall>x y. x \<in> f \<longrightarrow>(\<exists>x' y'. x'=Normal x \<and> y' = Normal y \<and> (x',y')\<in> g) \<longrightarrow> y \<in> f)"


definition Norm:: "(('s,'f) tran) set \<Rightarrow> bool" where
  "Norm \<equiv> \<lambda>g. (\<forall>x y. (x, y) \<in> g \<longrightarrow> (\<exists>x' y'. x=Normal x' \<and> y=Normal y'))"

definition env_tran::
    "('p \<Rightarrow> ('s, 'p, 'f) LanguageCon.com option)
     \<Rightarrow> ('s set)
        \<Rightarrow> (('s, 'p, 'f) LanguageCon.com \<times> ('s, 'f) xstate) list
           \<Rightarrow> ('s,'f) tran set \<Rightarrow> bool"
where
"env_tran \<Gamma> q l rely \<equiv> snd(l!0) \<in> Normal ` q \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                  
                   (snd(l!i), snd(l!(Suc i))) \<in> rely)
"

definition env_tran_right::
    "('p \<Rightarrow> ('s, 'p, 'f) LanguageCon.com option)     
        \<Rightarrow> (('s, 'p, 'f) LanguageCon.com \<times> ('s, 'f) xstate) list
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
  have "\<forall>ps psa n. if n < length ps then (ps @ psa) ! n = (ps ! n::('b, 'a, 'c) LanguageCon.com \<times> ('b, 'c) xstate) else (ps @ psa) ! n = psa ! (n - length ps)"
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


lemma skip_fault_tran_false:
assumes a0:"(\<Gamma>,l) \<in> cptn" and
        a1:"Suc i<length l \<and> l!i=(Skip, t) \<and> (\<forall>t'. \<not>(t=Normal t'))" and
        a2: "env_tran_right \<Gamma> l rely \<and> Norm rely" and 
        a3: "\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>c\<^sub>e (l!(Suc i))"
shows "P"
proof -
  from a3 have "\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<or> \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i))"
  using step_ce_elim_cases by blast
  thus ?thesis
  proof
    assume "\<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow>\<^sub>e (l ! Suc i)"
    thus ?thesis using a2 a1 unfolding env_tran_right_def Norm_def by fastforce
  next
    assume "\<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow> (l ! Suc i)"
    thus ?thesis using a1 by (metis (full_types) stepc_elim_cases(1)) 
  qed 
qed

lemma skip_fault_last:
assumes a0:"(\<Gamma>,l) \<in> cptn" and
        a1:"(i< (length l)) \<and> (l!i)=(Skip, t) \<and> (\<forall>t'. \<not>(t=Normal t'))" and
        a2: "env_tran_right \<Gamma> l rely \<and> Norm rely" 
shows "i=((length l)-1)"
proof (cases "i = ((length l)-1)")
  case True thus ?thesis .
next
  case False 
  have "0 < length l" using a1 by auto
  then obtain x xs where l:"l=x#xs"
    by (meson gr0_conv_Suc length_Suc_conv) 
  then have suci:"Suc i < length l" using False a1 by fastforce
  then have "\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>c\<^sub>e (l!(Suc i))" 
    using a0 a1 cptn_stepc_rtran l by blast
  thus ?thesis using a0 a1 a2 skip_fault_tran_false suci by blast    
qed

lemma env_tran_normal:
assumes a0:"env_tran_right \<Gamma> l rely \<and> Norm rely" and
        a1:"Suc i < length l \<and>  \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))"
shows "\<exists>s1 s2. snd(l!i) = Normal s1 \<and> snd(l!(Suc i)) = Normal s2"
using a0 a1 unfolding env_tran_right_def Norm_def by fastforce

lemma no_env_tran_not_normal:
assumes a0:"env_tran_right \<Gamma> l rely \<and> Norm rely" and
        a1:"Suc i < length l \<and>  \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))" and
        a2:"(\<forall>s1. \<not> (snd(l!i) = Normal s1)) \<or> (\<forall>s2. \<not> (snd (l!Suc i) = Normal s2))"
shows "P"
using a0 a1 a2 unfolding env_tran_right_def Norm_def by fastforce 
 
definition assum :: 
  "('s set \<times> ('s,'f) tran set) \<Rightarrow>
   'f set \<Rightarrow>
     (('s,'p,'f) confs) set" where
  "assum \<equiv> \<lambda>(pre, rely) F. 
             {c. snd((snd c)!0) \<in> Normal ` pre \<and> 
                 (\<forall>i. Suc i<length (snd c) \<longrightarrow> 
                 (fst c)\<turnstile>\<^sub>c((snd c)!i)  \<rightarrow>\<^sub>e ((snd c)!(Suc i)) \<longrightarrow>                  
                   (snd((snd c)!i), snd((snd c)!(Suc i))) \<in>  rely)}"

definition assum1 :: 
  "('s set \<times> ('s,'f) tran set) \<Rightarrow>
   'f set \<Rightarrow>
     (('s,'p,'f) confs) set" where
  "assum1 \<equiv> \<lambda>(pre, rely) F. 
             {(\<Gamma>,comp). snd(comp!0) \<in> Normal ` pre \<and> 
                 (\<forall>i. Suc i<length comp \<longrightarrow> 
                  \<Gamma>\<turnstile>\<^sub>c(comp!i)  \<rightarrow>\<^sub>e (comp!(Suc i)) \<longrightarrow>                  
                   (snd(comp!i), snd(comp!(Suc i))) \<in>  rely)}"


lemma assum_R_R': 
  "(\<Gamma>, l) \<in> assum(p, R) F \<Longrightarrow>
    snd(l!0) \<in> Normal `  p' \<Longrightarrow>
    R \<subseteq> R'  \<Longrightarrow> 
   (\<Gamma>, l) \<in> assum(p', R') F"
proof -
assume a0:"(\<Gamma>, l) \<in> assum(p, R) F" and
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
   (\<Gamma>,(P,s)#(P,t)#l) \<in> assum (p,R) F \<Longrightarrow>
   Sta p R \<and> Norm R \<Longrightarrow>
   \<exists>t1. t=Normal t1 \<and> t1 \<in> p
  " 
proof -
assume a0: "(\<Gamma>,(P,s)#(P,t)#l)\<in>cptn" and
         a1: "(\<Gamma>,(P,s)#(P,t)#l) \<in> assum (p,R) F" and
         a2: "Sta p R  \<and> Norm R"
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
         using a2 unfolding Norm_def
         by fastforce
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
   (\<Gamma>,(P,s)#(P,t)#l) \<in> assum (p,R) F \<Longrightarrow>
   Sta p R \<and> Norm R \<Longrightarrow>
   (\<Gamma>,(P,t)#l) \<in> assum (p,R) F
  " 
proof -
  assume a0: "(\<Gamma>,(P,s)#(P,t)#l)\<in>cptn" and
         a1: "(\<Gamma>,(P,s)#(P,t)#l) \<in> assum (p,R) F" and
         a2: "Sta p R \<and> Norm R"
  
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
   (\<Gamma>,(P,s)#(Q,t)#l) \<in> assum (p,R) F \<Longrightarrow>
   t \<in> Normal ` q \<Longrightarrow>
   (\<Gamma>,(Q,t)#l) \<in> assum (q,R) F
  " 
proof -
  assume a0: "(\<Gamma>,(P,s)#(Q,t)#l)\<in>cptn" and
         a1: "(\<Gamma>,(P,s)#(Q,t)#l) \<in> assum (p,R) F" and
         a2: "t \<in> Normal ` q"  
  then have "env_tran_right \<Gamma> ((P,s)#(Q,t)#l) R"
    using env_tran_right_def a1 unfolding assum_def
    by force
  then have "env_tran_right \<Gamma> ((Q,t)#l) R"
    using env_tran_tail by auto
  thus ?thesis using a2 unfolding assum_def env_tran_right_def by auto
qed
            
lemma sub_assum:
  assumes a0: "(\<Gamma>,(x#l0)@l1) \<in> assum (p,R) F"
  shows "(\<Gamma>,x#l0) \<in> assum (p,R) F"    
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
  assumes a0: "(\<Gamma>,l0@x1#l1) \<in> assum (p,R) F" and
          a1: "(snd x1) \<in> Normal ` q"
  shows "(\<Gamma>,x1#l1) \<in> assum (q,R) F"
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
     (('s,'p,'f) confs) set" where
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
     (('s,'p,'f) confs) set" where
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

definition com_validity :: 
  "('s,'p,'f) body \<Rightarrow>  'f set \<Rightarrow> ('s,'p,'f) com \<Rightarrow> 
    's set \<Rightarrow> (('s,'f) tran) set \<Rightarrow>  (('s,'f) tran) set \<Rightarrow>  
    's set \<Rightarrow>  's set \<Rightarrow>  bool" 
    ("_ \<Turnstile>\<^bsub>'/_\<^esub>/ _ sat [_,_, _, _,_]" [61,60,0,0,0,0,0,0] 45) where
  "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a] \<equiv> 
   \<forall>s. cp \<Gamma> Pr s \<inter> assum(p, R) F \<subseteq> comm(G, (q,a)) F"

definition com_cvalidity::
 "('s,'p,'f) body \<Rightarrow>
    ('s, 'p, 'f) sextuple set \<Rightarrow>
    'f set \<Rightarrow>
    ('s,'p,'f) com \<Rightarrow> 
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
definition All_End :: "('s,'p,'f) par_config \<Rightarrow> bool" where
  "All_End xs \<equiv> fst xs \<noteq>[] \<and> (\<forall>i<length (fst xs). final ((fst xs)!i,snd xs))"

definition par_assum :: 
  "('s set \<times>  
   (('s,'f) tran) set) \<Rightarrow>
   'f set \<Rightarrow>
   (('s,'p,'f) par_confs) set" where
  "par_assum \<equiv> 
     \<lambda>(pre, rely) F. {c. 
       snd((snd c)!0) \<in> Normal ` pre \<and> (\<forall>i. Suc i<length (snd c) \<longrightarrow> 
       (fst c)\<turnstile>\<^sub>p((snd c)!i)  \<rightarrow>\<^sub>e ((snd c)!(Suc i)) \<longrightarrow>        
         (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> rely)}"
           
definition par_comm :: 
  "((('s,'f) tran) set  \<times> 
     ('s set \<times> 's set))  \<Rightarrow> 
    'f set \<Rightarrow>
   (('s,'p,'f) par_confs) set" where
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
  "('s,'p,'f) body \<Rightarrow> 
   'f set \<Rightarrow>
   ('s,'p,'f) par_com \<Rightarrow>  
   ('s set) \<Rightarrow> 
   ((('s,'f) tran) set) \<Rightarrow> 
   ((('s,'f) tran) set) \<Rightarrow> 
   ('s set) \<Rightarrow>
   ('s set) \<Rightarrow> 
     bool"  
("_ \<Turnstile>\<^bsub>'/_\<^esub>/ _ SAT [_, _, _, _,_]" [61,60,0,0,0,0,0,0] 45) where
  "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Ps SAT [pre, R, G, q,a] \<equiv> 
   \<forall>s. par_cp \<Gamma> Ps s \<inter> par_assum(pre, R) F \<subseteq> par_comm(G, (q,a)) F"
   
definition par_com_cvalidity :: 
  "('s,'p,'f) body \<Rightarrow>
    ('s,'p,'f) sextuple set \<Rightarrow>
   'f set \<Rightarrow>
  ('s,'p,'f) par_com \<Rightarrow>   
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
lrghoare :: "[('s,'p,'f) body,
             ('s,'p,'f) sextuple set,
              'f set,
              ('s,'p,'f) com,  
              ('s set),  
              (('s,'f) tran) set, (('s,'f) tran) set,
              's set,
               's set] \<Rightarrow> bool"
    ("_,_ \<turnstile>\<^bsub>'/_\<^esub> _ sat [_, _, _, _,_]" [61,61,60,60,0,0,0,0] 45)
where
 Skip: "\<lbrakk> Sta q R; Norm R; (\<forall>s. (Normal s, Normal s) \<in> G) \<rbrakk> \<Longrightarrow>
         \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> Skip sat [q, R, G, q,a] "

|Spec: "\<lbrakk>p \<subseteq> {s. (\<forall>t. (s,t)\<in>r \<longrightarrow> t \<in> q) \<and> (\<exists>t. (s,t) \<in> r)};        
        (\<forall>s t. s\<in>p \<and> (s,t)\<in>r \<longrightarrow> (Normal s,Normal t) \<in> G);
        Sta p R;Sta q R; Norm R\<rbrakk> \<Longrightarrow> \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Spec r) sat [p, R, G, q,a]"

| Basic: "\<lbrakk> p \<subseteq> {s. f s \<in> q};            
           (\<forall>s t. s\<in>p \<and> (t=f s) \<longrightarrow> (Normal s,Normal t) \<in> G);
            Sta p R;Sta q R; Norm R \<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Basic f) sat [p, R, G, q,a]"

| If: "\<lbrakk> \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> b, R, G, q,a]; 
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [p \<inter> (-b), R, G, q,a];         
        Sta p R; Norm R;  (\<forall>s. (Normal s, Normal s) \<in> G)
        \<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Cond b c1 c2) sat [p,  R, G, q,a]"

| While: "\<lbrakk> \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p \<inter> b, R, G, p,a];            
            Sta p R; Sta (p \<inter> (-b)) R; Sta a R; Norm R; (\<forall>s. (Normal s,Normal s) \<in> G)\<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (While b c) sat [p, R, G, p \<inter> (-b),a]"

| Seq: "\<lbrakk> \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p, R, G, q,a]; \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [q, R, G, r,a];         
         Sta a R; Norm R; (\<forall>s. (Normal s,Normal s) \<in> G)\<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Seq c1 c2) sat [p, R, G, r,a]"

| Await: "\<lbrakk> \<forall>V. \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
                  (p \<inter> b \<inter> {V}) c 
                  ({s. (Normal V, Normal s) \<in> G} \<inter> q),
                  ({s. (Normal V, Normal s) \<in> G} \<inter> a);                                        
           Sta p R; Sta q R; Sta a R; Norm R\<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Await b c) sat [p, R, G, q,a]"

| Guard: "\<lbrakk> \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p \<inter> g, R, G, q,a];           
        Sta (p \<inter> g) R; Norm R; (\<forall>s. (Normal s, Normal s) \<in> G)\<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Guard f g c) sat [p \<inter> g, R, G, q,a]"

| Guarantee:  "\<lbrakk> \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p \<inter> g, R, G, q,a];
                Sta p R;f\<in>F; Norm R;(\<forall>s. (Normal s, Normal s) \<in> G) \<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Guard f g c) sat [p, R, G, q,a]"

| CallRec: "\<lbrakk>(c,p,R,G,q,a) \<in> Specs; 
             \<forall>(c,p,R,G,q,a)\<in> Specs. c \<in> dom \<Gamma> \<and> 
              Sta p R \<and>  (\<forall>s. (Normal s,Normal s) \<in> G) \<and> Norm R \<and>
             \<Gamma>,\<Theta> \<union> Specs \<turnstile>\<^bsub>/F\<^esub> (the (\<Gamma> c)) sat [p,  R, G, q,a];
            Sta p R; Norm R; (\<forall>s. (Normal s, Normal s) \<in> G)\<rbrakk> \<Longrightarrow>
            \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"

| Asm: "\<lbrakk>(c,p,R,G,q,a) \<in> \<Theta>\<rbrakk> 
        \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]" 

| Call: "\<lbrakk>c \<in> dom \<Gamma>; 
         \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (the (\<Gamma> c)) sat [p, R, G, q,a];         
         Sta p R; Norm R; (\<forall>s. (Normal s, Normal s) \<in> G)\<rbrakk> 
        \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"

| DynCom: "(\<forall>s \<in> p. (\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (c s) sat [p, R, G, q,a])) \<Longrightarrow>    
          (Sta p R) \<and> (Sta q R) \<and> (Sta a R) \<and>
           Norm R \<Longrightarrow> (\<forall>s. (Normal s,Normal s) \<in> G) \<Longrightarrow>
            \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (DynCom c) sat [p, R, G, q,a]"

| Throw: "\<lbrakk>Sta a R; Norm R; (\<forall>s. (Normal s, Normal s) \<in> G) \<rbrakk> \<Longrightarrow>
         \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> Throw sat [a,  R, G, q,a] "

| Catch: "\<lbrakk> \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p, R, G, q,r]; 
           \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [r, R, G, q,a];           
           Sta q R; Norm R; (\<forall>s. (Normal s, Normal s) \<in> G)\<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Catch c1 c2) sat [p, R, G, q,a]"

| Conseq: "\<forall>s \<in> p. 
             (\<exists>p' R' G' q' a'.  
             (s\<in> p') \<and>
              R \<subseteq> R' \<and>            
             G' \<subseteq> G \<and>             
             q' \<subseteq> q \<and>
             a' \<subseteq> a \<and>                        
            (\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p', R', G', q',a']) ) 
            \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q,a]"

| Conj_post: " \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q,a] \<Longrightarrow>
                \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q',a'] 
            \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q \<inter> q',a \<inter> a']" 

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


definition Pre :: " ('s,'p,'f)rgformula \<Rightarrow> ('s set)" where
  "Pre x \<equiv> fst(snd x)"

definition Post :: "('s,'p,'f) rgformula \<Rightarrow> ('s set)" where
  "Post x \<equiv>  fst(snd(snd(snd(snd x))))"

definition Abr ::  "('s,'p,'f) rgformula \<Rightarrow> ('s set)" where
  "Abr x \<equiv> snd(snd(snd(snd(snd x))))"

definition Rely :: "('s,'p,'f) rgformula \<Rightarrow> (('s,'f) tran) set" where
  "Rely x \<equiv> fst(snd(snd x))"

definition Guar ::  "('s,'p,'f) rgformula \<Rightarrow> (('s,'f) tran) set" where
  "Guar x \<equiv> fst(snd(snd(snd x)))"

definition Com :: "('s,'p,'f) rgformula \<Rightarrow> ('s ,'p,'f) com" where
  "Com x \<equiv> fst  x"


inductive
  par_rghoare ::  "[('s,'p,'f) body,
              ('s,'p,'f) sextuple set,
              'f set,
              ( ('s,'p,'f) rgformula) list,  
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
  assumes a3:"env_tran_right \<Gamma> l rely \<and> Norm rely"
  shows "fst (l!(Suc i)) =  Throw \<and> (\<exists>s2. snd(l!(Suc i)) = Normal s2)"
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
      assumes a4:"env_tran_right \<Gamma> l rely \<and> Norm rely" 
      shows "fst (l!j) = Throw \<and> (\<exists>s2. snd(l!j) = Normal s2)"
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
  moreover then have "j  - i = Suc n"by (simp add: Suc.prems(3))
  ultimately have "fst (l ! (j)) = LanguageCon.com.Throw \<and> (\<exists>s2. snd(l!j) = Normal s2)" 
    using Suc throw_suc_i[of \<Gamma> l i s1]
    by (metis (no_types, lifting) Suc_diff_Suc Suc_eq_plus1 Suc_leI l_suc diff_Suc_1)        
  also have "j=j" using Cons using Suc.prems(2) by linarith  
  ultimately show ?case using Suc by (metis (no_types))
qed    

lemma only_one_component_tran_j:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!i) = Skip  \<or> (fst (l!i) = Throw \<and> snd(l!i) = Normal s1)" and 
         a2: "i\<le>j \<and> Suc j < length l" and
         a3: "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" and 
         a4: "env_tran_right \<Gamma> l rely \<and> Norm rely"    
   shows "P"
proof -   
   have "fst (l!j) = Skip  \<or> (fst (l!i) = Throw \<and> snd(l!i) = Normal s1)" 
   using a0 a1  a2 a3 a4 i_skip_all_skip by fastforce           
   also have "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" using a3 by fastforce 
   ultimately show ?thesis
by (meson SmallStepCon.final_def SmallStepCon.no_step_final' Suc_lessD a0 a2  a4 i_throw_all_throw)  
qed     

lemma only_one_component_tran_all_j:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!i) = Skip  \<or> (fst (l!i) = Throw \<and> snd(l!i) = Normal s1)" and 
         a2: "Suc i<length l" and
         a3: "\<forall>j. i\<le>j \<and> Suc j < length l \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"  and
         a4: "env_tran_right \<Gamma> l rely \<and> Norm rely"              
   shows "P" 
using a0 a1 a2 a3 a4  only_one_component_tran_j 
by (metis lessI less_Suc_eq_le) 


lemma zero_skip_all_skip: 
      assumes a1:"(\<Gamma>, l) \<in> cptn \<and> fst (l!0) = Skip \<and>  i < length l"
      shows "fst (l!i) = Skip"
using a1 i_skip_all_skip by blast

lemma zero_throw_all_throw:
      assumes a1:"(\<Gamma>, l) \<in> cptn \<and> fst (l!0) = Throw \<and> snd(l!0) = Normal s1 \<and>  i < length l"
      assumes a2: "env_tran_right \<Gamma> l rely \<and> Norm rely" 
      shows "fst (l!i) = Throw \<and> (\<exists>s2. snd (l!i) = Normal s2)"
using a1 a2 i_throw_all_throw by (metis le0) 

lemma only_one_component_tran_0:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "(fst (l!0) = Skip) \<or> (fst (l!0) = Throw \<and> snd(l!0) = Normal s1)" and                  
         a2: "Suc j < length l" and
         a3: "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"  and
         a4: "env_tran_right \<Gamma> l rely \<and> Norm rely"         
   shows "P"         
   using Suc_lessD a0 a1 a2 a3 a4 
        prod.collapse stepc_elim_cases(1) zero_skip_all_skip zero_throw_all_throw
  proof -
    have "\<forall>n na. \<not> Suc n < na \<or> n < na"
      by (metis Suc_lessD)
    hence "j < length l"
      by (metis a2)
    hence False
      by (meson SmallStepCon.final_def SmallStepCon.no_step_final' a0 a1 a3 a4 zero_skip_all_skip zero_throw_all_throw)
    thus ?thesis
      by meson
  qed

lemma only_one_component_tran_all_j_i:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!i) = Skip \<or> (fst (l!0) = Throw \<and> snd(l!0) = Normal s1)" and 
         a2: "Suc i<length l" and
         a3: "\<forall>j. j\<ge>i \<and> Suc j < length l \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" and
         a4: "env_tran_right \<Gamma> l rely \<and> Norm rely"      
   shows "P" 
using a0 a1 a2 a3 a4
proof (induct i)
  case 0 
  have "(0::nat) \<le> 0" by fastforce  thus ?thesis using only_one_component_tran_0 0 by metis
next
  case (Suc n) thus ?thesis
    by (metis Suc_leI lessI only_one_component_tran_0 prod.collapse stepc_elim_cases(1))
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
              a2: "fst (l!0) = Skip \<or> (fst (l!0) = Throw \<and> snd(l!0) = Normal s1)" and
              a3: "Suc i < length l" and
              a4: "env_tran_right \<Gamma> l rely \<and> Norm rely"
      shows "\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))"
proof -
   have "\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>c\<^sub>e (l!(Suc i))" using a1 a2 a3 cptn_tran_ce_i by auto   
   also have "\<not> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" using a1 a2 a3 a4 using only_one_component_tran_0 by metis           
   ultimately show ?thesis by (simp add: step_ce.simps) 
qed

lemma final_always_env_i: 
      assumes a1:"(\<Gamma>, l) \<in> cptn" and
              a2: "fst (l!i) = Skip \<or> (fst (l!i) = Throw \<and> snd(l!i) = Normal s1)" and
              a3: "j\<ge>i \<and> Suc j<length l" and
              a4: "env_tran_right \<Gamma> l rely \<and> Norm rely"
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
         using a1 a2 a3 a4 only_one_component_tran_j [of \<Gamma> l i s1 j rely]  by blast
      then show ?thesis using a01 ce_tran by (simp add: step_ce.simps) 
   qed
qed


subsection {*Skip Sound*}

lemma stable_q_r_q: 
  assumes a0:"Sta q R \<and> Norm R"  and       
          a1: "snd(l!i) \<in> Normal ` q" and
          a2:"(snd(l!i), snd(l!(Suc i))) \<in> R"
  shows "snd(l!(Suc i)) \<in> Normal ` q"
using a0  a1  a2 
unfolding Sta_def Norm_def  by fastforce 

lemma stability:
assumes   a0:"Sta q R \<and> Norm R"  and                 
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
  assumes a0:"Sta q R \<and> Norm R"  and                 
          a1: "snd(l!i) \<in> Normal ` q" and
          a2: "i<j \<and> j < (length l)" and
          a3: "n=j-i-1" and
          a4: "\<forall>k\<ge>i. k < j \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))" and
          a5: "env_tran_right \<Gamma> l R"
      shows "snd (l!j) \<in> Normal ` q"
using a0 a1 a2 a3 a4 a5  by (meson less_imp_le_nat  stability)

  
lemma stable_only_env_1: 
  assumes a0:"Sta q R \<and> Norm R"  and                 
          a1: "snd(l!i) \<in> Normal ` q" and
          a2: "i<j \<and> j < (length l)" and
          a3: "n=j-i-1" and
          a4: "\<forall>i. Suc i < length l \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))" and
          a5: "env_tran_right \<Gamma> l R"
      shows "snd (l!j) \<in> Normal ` q"
using a0 a1 a2 a3 a4 a5 
by (meson stable_only_env_i_j less_trans_Suc)


lemma stable_only_env_q: 
  assumes a0:"Sta q R \<and> Norm R"  and                 
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



lemma Skip_sound: 
  "Sta q R \<and> Norm R \<Longrightarrow>       
   (\<forall>s. (Normal s, Normal s) \<in> G)  \<Longrightarrow>
   \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Skip sat [q,R, G, q,a]"
proof -  
 assume
    a0:"Sta q R \<and> Norm R" and    
    a1:"(\<forall>s. (Normal s, Normal s) \<in> G)"
  {
    fix s
    have ass:"cp \<Gamma> Skip s \<inter> assum(q, R) F \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cp \<Gamma> Skip s" and a11:"c \<in> assum(q, R) F"
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof - 
      {assume "snd (last l) \<notin> Fault ` F"
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
           have env_right:"env_tran_right \<Gamma> l R \<and> Norm R" using  a0 env_tran_right_def assum cp by metis
           then have all_tran_env: "\<forall>i. Suc i < length l \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))"
           using final_always_env_i cp  by (simp add: cp zero_final_always_env_0)
           then have "\<forall>i. i < length l \<longrightarrow> snd (l!i) \<in> Normal ` q"
           using stable_only_env_q  a0  env  by fastforce
           thus ?thesis using last_l using len_l by fastforce    
         qed                
         note res = conjI [OF fst_last_skip last_q]
       } thus ?thesis by auto qed
       note res = conjI [OF concl concr]               
      }              
      thus ?thesis using c_prod unfolding comm_def by auto qed      
    } thus ?thesis by auto qed 
  } thus ?thesis by (simp add: com_validity_def[of \<Gamma>] com_cvalidity_def) 
qed

lemma Throw_sound: 
  "Sta a R \<and> Norm R \<Longrightarrow>
   (\<forall>s. (Normal s, Normal s) \<in> G) \<Longrightarrow>
   \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Throw sat [a, R, G, q,a]"
proof -  
 assume   
    a1:"Sta a R \<and> Norm R" and
    a2:" (\<forall>s. (Normal s, Normal s) \<in> G)" 
  {
    fix s
    have "cp \<Gamma> Throw s \<inter> assum(a, R) F \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cp \<Gamma> Throw s" and a11:"c \<in> assum(a, R) F"
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof - 
      {assume "snd (last l) \<notin> Fault ` F"
       have cp:"l!0=(Throw,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
       have assum:"snd(l!0) \<in> Normal ` (a) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                   (snd(l!i), snd(l!(Suc i))) \<in> (R))" 
       using a11 c_prod unfolding assum_def by simp
       then have env_tran:"env_tran_right \<Gamma> l R" using cp env_tran_right_def by auto
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
             using cp a1 assum env_tran asuci zero_throw_all_throw by metis
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
            by (metis (no_types, lifting) a1 One_nat_def assum cp diff_Suc_less env_tran fst_conv imageE len_l zero_throw_all_throw)                        
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
      thus ?thesis using c_prod unfolding comm_def by auto qed      
    } thus ?thesis by auto qed 
  } thus ?thesis by (simp add: com_validity_def[of \<Gamma>] com_cvalidity_def) 
qed

lemma no_comp_tran_before_i_0_g:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!0) = c" and         
         a2: "Suc i<length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "j < i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" and
         a4: "\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))" and
         a5: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> ((c1=Skip) \<or> ((c1=Throw) \<and> (\<exists>s21. s2 = Normal s21)))" and
         a6: "env_tran_right \<Gamma> l rely \<and> Norm rely"
   shows "P"
  proof -
   have "Suc j < length l" using a0 a1 a2 a3 a4 by fastforce
   then have "fst (l!j) = c" 
     using a0 a1 a2 a3 a4 cptn_env_same_prog[of \<Gamma> l j] by fastforce
   then obtain s s1 p where l_0: "l!j = (c, s) \<and> l!(Suc j) = (p,s1)"  
     by (metis (no_types) prod.collapse)    
    then have suc_0_skip: "fst (l!Suc j) = Skip \<or> (fst (l!Suc j) = Throw \<and> (\<exists>s2. snd(l!Suc j) = Normal s2))" 
      using a5 a3 SmallStepCon.step_Stuck_prop by fastforce 
   thus ?thesis using only_one_component_tran_j
    proof -
      have "\<forall>n na. \<not> n < na \<or> Suc n \<le> na"
        using Suc_leI by satx  
      thus ?thesis using only_one_component_tran_j suc_0_skip a6 a0 a2 a3 by metis       
    qed
qed

lemma no_comp_tran_before_i:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = c" and        
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "k\<le>j \<and> j < i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" and
         a4: "\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))" and
         a5: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> ((c1=Skip)\<or> ((c1=Throw) \<and> (\<exists>s21. s2 = Normal s21)))" and
         a6: "env_tran_right \<Gamma> l rely \<and> Norm rely"
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
  moreover have "env_tran_right \<Gamma> l1 rely \<and> Norm rely" using Suc(8) l unfolding env_tran_right_def by fastforce
  ultimately show ?case using Suc(1)[of l1 i' j' ] Suc(7) by auto
qed

lemma exists_first_occ: "P (n::nat) \<Longrightarrow> \<exists>m. P m \<and> (\<forall>i<m. \<not> P i)"
proof (induct n)
  case 0 thus ?case by auto
next
  case (Suc n) thus ?case
  by (metis ex_least_nat_le not_less0) 
qed

lemma exist_first_comp_tran:
assumes a0:"(\<Gamma>, l) \<in> cptn" and
        a1: "Suc i<length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))"      
shows "\<exists>j. j\<le>i \<and>  (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<and> (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
using a0 a1 
proof (induct i arbitrary: l)
  case 0 thus ?case by fastforce
next
  case (Suc n)
  then have len_l:"length l>2" by fastforce
  then obtain a1 a2 l1 where l1:"l=a1#a2#l1"
    using three_elems_list by fastforce
  have "Suc 0 < length l"
    using len_l by linarith
  then have ce:"\<Gamma>\<turnstile>\<^sub>c l ! 0 \<rightarrow>\<^sub>c\<^sub>e (l ! Suc 0)" 
    by (simp add: Suc.prems(1) cptn_tran_ce_i)  
  then have ce_1:"\<Gamma>\<turnstile>\<^sub>c l ! 0 \<rightarrow> (l ! Suc 0) \<or> \<Gamma>\<turnstile>\<^sub>c l ! 0 \<rightarrow>\<^sub>e (l ! Suc 0)"
    by (simp add: step_ce.simps) 
  thus ?case 
  proof     
    assume "\<Gamma>\<turnstile>\<^sub>c (l ! 0) \<rightarrow> (l ! Suc 0)" 
    then show ?thesis by fastforce 
  next      
    assume env_0:"\<Gamma>\<turnstile>\<^sub>c (l ! 0) \<rightarrow>\<^sub>e (l ! Suc 0)"       
    have "(\<Gamma>,a2#l1)\<in>cptn"
      using l1 Suc.prems(1) cptn_dest_pair by blast        
    then have "\<exists>j\<le>n. (\<Gamma>\<turnstile>\<^sub>c ((a2#l1) ! j) \<rightarrow> ((a2#l1) ! Suc j)) \<and>
              (\<forall>k<j. \<Gamma>\<turnstile>\<^sub>c (a2#l1) ! k \<rightarrow>\<^sub>e ((a2#l1) !  Suc k))" 
      using l1 Suc(1)[of "a2#l1"] Suc(2) Suc(3) by auto
    then obtain j where induct:"j\<le>n \<and> (\<Gamma>\<turnstile>\<^sub>c ((a2#l1) ! j) \<rightarrow> ((a2#l1) ! Suc j)) \<and>
                                (\<forall>k<j. \<Gamma>\<turnstile>\<^sub>c (a2#l1) ! k \<rightarrow>\<^sub>e ((a2#l1) ! Suc k))" by auto
    then have j_m_n:"Suc j\<le> Suc n" by auto
    thus ?thesis 
    proof
    {
      assume a00:"Suc j\<le>Suc n"
      then have sucj:"Suc (Suc j) < length l" using Suc(3) by fastforce
      then have p1:"\<Gamma>\<turnstile>\<^sub>c l ! (Suc j) \<rightarrow> (l ! Suc (Suc j))" 
        using induct l1  a00 tl_zero by fastforce
      then have p2: "(\<forall>k<(Suc j). \<Gamma>\<turnstile>\<^sub>c l ! k \<rightarrow>\<^sub>e (l ! Suc k))"
        using  induct env_0 sucj l1 for_all_k_sublist[of j l] by auto                
      then have "\<Gamma>\<turnstile>\<^sub>c l ! (Suc j) \<rightarrow> (l ! Suc (Suc j)) \<and> 
               (\<forall>k<(Suc j). \<Gamma>\<turnstile>\<^sub>c l ! k \<rightarrow>\<^sub>e (l ! Suc k))"
      using p1 p2 by auto
    } thus ?thesis using j_m_n by auto qed   
  qed
qed

lemma only_one_component_tran1:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!0) = c" and         
         a2: "Suc i<length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "j \<noteq> i \<and> Suc j < length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" and
         a4: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> ((c1=Skip)\<or> ((c1=Throw) \<and> (\<exists>s21. s2 = Normal s21)))" and
         a5: "env_tran_right \<Gamma> l rely \<and> Norm rely"
   shows "P"
proof (cases "j=i")
  case True thus ?thesis using a3 by auto
next
  case False note j_neq_i=this 
  thus ?thesis
  proof (cases "j<i")
    case True 
    note j_l_i = this
    obtain j1 
    where all_ev:"j1\<le>i \<and>  
                 (\<Gamma>\<turnstile>\<^sub>c(l!j1)  \<rightarrow> (l!(Suc j1))) \<and> 
                 (\<forall>k < j1. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
    using a0 a2 exist_first_comp_tran by blast
    thus ?thesis 
    proof (cases "j1=i")      
      case True 
      then have "(\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
        using j_l_i  all_ev by auto
      thus ?thesis using no_comp_tran_before_i a0 a1 a2 a3 a4 a5
                           j_l_i by blast
    next
      case False 
      then have "j1<i" using all_ev by auto
      thus ?thesis           
        using no_comp_tran_before_i a0 a1 a2 a3 a4 a5
                 j_l_i  all_ev by blast
     qed 
  next
    case False 
    obtain j1 
    where all_ev:"j1\<le>j \<and>  
                 (\<Gamma>\<turnstile>\<^sub>c(l!j1)  \<rightarrow> (l!(Suc j1))) \<and> 
                 (\<forall>k < j1. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
      using a0 a3 exist_first_comp_tran by blast
    thus ?thesis 
    proof (cases "j1=j")      
      case True       
      then have all_j_env:"(\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
        using  all_ev by auto
      then have "i < j" using j_neq_i False by fastforce
      thus ?thesis using False no_comp_tran_before_i a0 a1 a2 a3 a4 a5
                          all_j_env   
                          dual_order.strict_trans by blast 
    next
      case False 
      then have "j1<j" using all_ev by auto
      thus ?thesis           
        using no_comp_tran_before_i a0 a1 a2 a3 a4 a5 all_ev 
        by blast
     qed       
  qed
qed  
 
lemma only_one_component_tran_i:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = c" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "k\<le>j \<and> j \<noteq> i \<and> Suc j < length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" and
         a4: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> ((c1=Skip)\<or> ((c1=Throw) \<and> (\<exists>s21. s2 = Normal s21)))" and
         a5: "env_tran_right \<Gamma> l rely \<and> Norm rely"
   shows "P"
using a0 a1 a2 a3 a4 a5
proof (induct k arbitrary: l i j)
  case 0 thus ?thesis using only_one_component_tran1[of \<Gamma> l c i j] by blast
next
  case (Suc n) 
   then obtain a1 l1 where l: "l=a1#l1"
    by (metis less_nat_zero_code list.exhaust list.size(3))
  then have l1notempty:"l1\<noteq>[]" using Suc by force    
  then obtain i' where i': "i=Suc i'" using Suc 
    using less_imp_Suc_add using Suc_le_D by blast 
  then obtain j' where j': "j=Suc j'" using Suc
    using Suc_le_D by blast      
  have "(\<Gamma>,l1)\<in>cptn" using Suc l
    using tl_in_cptn l1notempty by blast
  moreover have "fst (l1 ! n) = c"
    using Suc l l1notempty by force  
  moreover have "Suc i' < length l1 \<and> n \<le> i' \<and> \<Gamma>\<turnstile>\<^sub>c l1 ! i' \<rightarrow> (l1 ! Suc i')"
    using Suc l l1notempty i' by auto
  moreover have "n \<le> j' \<and> j' \<noteq> i' \<and> Suc j' < length l1 \<and> \<Gamma>\<turnstile>\<^sub>c l1 ! j' \<rightarrow> (l1 ! Suc j')"
    using Suc l l1notempty i' j' by auto
  moreover have "env_tran_right \<Gamma> l1 rely" using Suc(7) l unfolding env_tran_right_def by fastforce
  ultimately show ?case using Suc by blast
qed

lemma only_one_component_tran:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = c" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "k\<le>j \<and> j \<noteq> i \<and> Suc j < length l" and
         a4: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> ((c1=Skip)\<or> ((c1=Throw) \<and> (\<exists>s21. s2 = Normal s21)))" and
         a5: "env_tran_right \<Gamma> l rely \<and> Norm rely"
   shows "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
using a0 a1 a2 a3 a4 a5 only_one_component_tran_i
proof -
  {assume "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<or> (\<not> \<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"
   then have  "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
   proof
     assume "\<Gamma>\<turnstile>\<^sub>c l ! j \<rightarrow> (l ! Suc j)" 
       thus ?thesis using a0 a1 a2 a3 a4 a5 only_one_component_tran_i
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
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> ((c1=Skip)\<or> ((c1=Throw) \<and> (\<exists>s21. s2 = Normal s21)))" and
         a4: "env_tran_right \<Gamma> l rely \<and> Norm rely"
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof -
  {fix j
  assume "k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l)"
  then have "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))" 
    using only_one_component_tran a0 a1 a2 a3 a4 by blast
  } thus ?thesis by auto
qed

lemma only_one_component_tran_all_not_comp:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = c" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> ((c1=Skip)\<or> ((c1=Throw) \<and> (\<exists>s21. s2 = Normal s21)))" and
         a4: "env_tran_right \<Gamma> l rely \<and> Norm rely"
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"
proof -
  {fix j
  assume "k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l)"
  then have "\<not>(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" 
    using only_one_component_tran_i a0 a1 a2 a3 a4 by blast
  } thus ?thesis by auto
qed

lemma final_exist_component_tran:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
          a1: "fst (l!i) = c" and               
          a2: "env_tran \<Gamma> q l R \<and> Norm R" and
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

lemma final_exist_component_tran_final:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and                                  
          a2: "i\<le>j \<and> j < length l \<and> final (l!j)" and                   
          a3: "\<not>final(l!i)" and 
          a4: "env_tran_right \<Gamma> l R \<and> Norm R"            
  shows "\<exists>k. k\<ge>i \<and> k<j \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))) \<and> final(l!(Suc k))"
proof -
  {assume "\<forall>k. k\<ge>i \<and>  k<j \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)) \<and> final(l!(Suc k)))" 
   then have a01:"\<forall>k. k\<ge>i \<and>  k<j \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))) \<or> 
                                     ((\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))) \<and> \<not>final(l!(Suc k)))"
   by (metis (no_types, lifting) Suc_eq_plus1 a0 a2 cptn_tran_ce_i less_trans_Suc step_ce_elim_cases)
   {
     assume a00:"i=j"
     then have "fst (l!j) =  fst (l!i)"  
     using a0 a2  by auto
     then have False using a00 a2 a3 by blast  
   } note 1=this
   {
     assume not_i_j:"i\<noteq>j"
     then have i_j:"i<j" using a2 by arith    
     then have False using a01 a2  a3
     proof (induct "j-i-1" arbitrary: j i) 
       case 0       
       then have suci_j:"Suc i = j" using 0 by auto
       have s1:"\<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow>\<^sub>e l ! Suc i \<or>
                 \<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow> l ! Suc i \<and> \<not> SmallStepCon.final (l ! Suc i)"
       using 0 by auto
       {assume a00:"\<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow>\<^sub>e l ! Suc i"
        then have "fst (l!i) = fst (l!Suc i)" 
          by (metis (no_types) env_c_c' prod.collapse)
        then have ?thesis using 0 a00 suci_j a4 no_env_tran_not_normal
          by (metis SmallStepCon.final_def)
       } note s2=this                                   
       {assume "\<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow> l ! Suc i \<and> \<not> SmallStepCon.final (l ! Suc i)"
           then have ?thesis using 0 suci_j by auto
        } thus ?thesis using s1 s2 by auto         
     next
       case (Suc x)
       then have "x = j - (i + 1) -1" by arith             
       moreover have 
       "\<forall>k. (Suc i) \<le> k \<and> k < j \<longrightarrow>
          \<Gamma>\<turnstile>\<^sub>c l ! k \<rightarrow>\<^sub>e l ! Suc k \<or>
          \<Gamma>\<turnstile>\<^sub>c l ! k \<rightarrow> l ! Suc k \<and> \<not> SmallStepCon.final (l ! Suc k)"
       using Suc by auto
       moreover have "Suc i < j" using Suc by arith
       moreover have "j<length l" using Suc by arith
       moreover have "final (l!j)" using Suc by auto
       moreover have "\<not>final (l!Suc i)"         
       proof - 
          have s1:"\<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow>\<^sub>e l ! Suc i \<or>
                 \<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow> l ! Suc i \<and> \<not> SmallStepCon.final (l ! Suc i)"
          using Suc by auto
          {assume a00:"\<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow>\<^sub>e l ! Suc i"
           then have "fst (l!i) = fst (l!Suc i)" 
             by (metis (no_types) env_c_c' prod.collapse)
           then have ?thesis using Suc a4 a00  no_env_tran_not_normal
             by (metis (no_types) SmallStepCon.final_def less_trans_Suc)
          } note s2=this                                   
          {assume "\<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow> l ! Suc i \<and> \<not> SmallStepCon.final (l ! Suc i)"
           then have ?thesis by auto
          } thus ?thesis using s1 s2 by auto 
       qed
       ultimately show ?case using Suc(1)[of j "i+1" ]
         by fastforce
    qed
   } note 2 = this
   then have False using 1 by auto
  }  
  thus ?thesis  by auto
qed 


subsection {* Basic Sound *}

lemma basic_skip:
   "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Basic f,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> c1=Skip"
proof -
  {fix s1 s2 c1
   assume "\<Gamma>\<turnstile>\<^sub>c(Basic f,s1)  \<rightarrow> ((c1,s2))"     
   then have "c1=Skip" using stepc_elim_cases(3) by blast    
  } thus ?thesis by auto 
qed  

lemma no_comp_tran_before_i_basic:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Basic f" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "k\<le>j \<and> j < i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" and
         a4: "\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))" and
         a5: "env_tran_right \<Gamma> l rely \<and> Norm rely" 
   shows "P"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Basic f,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  basic_skip by blast                  
  thus ?thesis using  a0 a1 a2 a3 a4 a5 no_comp_tran_before_i by blast
qed

lemma only_one_component_tran_i_basic:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Basic f" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "k\<le>j \<and> j \<noteq> i \<and> Suc j < length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" and
         a4: "env_tran_right \<Gamma> l rely \<and> Norm rely"       
   shows "P"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Basic f,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  basic_skip by blast
  thus ?thesis using  a0 a1 a2 a3 a4 only_one_component_tran_i by blast
qed   

lemma only_one_component_tran_basic:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Basic f" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "k\<le>j \<and> j \<noteq> i \<and> Suc j < length l" and
         a4: "env_tran_right \<Gamma> l rely \<and> Norm rely"       
   shows "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Basic f,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  basic_skip by blast
  thus ?thesis using  a0 a1 a2 a3 a4 only_one_component_tran by blast
qed   

lemma only_one_component_tran_all_env_basic:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Basic f" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and         
         a3: "env_tran_right \<Gamma> l rely \<and> Norm rely"       
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Basic f,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  basic_skip by blast
  thus ?thesis using  a0 a1 a2 a3  only_one_component_tran by blast
qed   

lemma only_one_component_tran_all_not_comp_basic:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Basic f" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and         
         a3: "env_tran_right \<Gamma> l rely \<and> Norm rely"       
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Basic f,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  basic_skip by blast
  thus ?thesis using  a0 a1 a2 a3 only_one_component_tran_all_not_comp by blast
qed   

lemma final_exist_component_tran_basic:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
          a1: "fst (l!i) = Basic f" and               
          a2: "env_tran \<Gamma> q l R \<and> Norm R" and
          a3: "i\<le>j \<and> j < length l \<and> final (l!j)" 
  shows "\<exists>k. k\<ge>i \<and> k<j \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
proof - 
  show ?thesis using  a0 a1 a2 a3 final_exist_component_tran by blast
qed   

lemma Basic_sound: 
       "p \<subseteq> {s. f s \<in> q} \<Longrightarrow>
      (\<forall>s t. s\<in>p \<and> (t=f s) \<longrightarrow> (Normal s,Normal t) \<in> G) \<Longrightarrow>       
       Sta p R \<and> Norm R \<Longrightarrow>
       Sta q R \<Longrightarrow>       
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  (Basic f) sat [p, R, G, q,a]"
proof -  
 assume
    a0:"p \<subseteq> {s. f s \<in> q}" and
    a1:"(\<forall>s t. s\<in>p \<and> (t=f s) \<longrightarrow> (Normal s,Normal t) \<in> G)" and
    a2:"Sta p R \<and> Norm R" and
    a3:"Sta q R" 
{
    fix s
    have "cp \<Gamma> (Basic f) s \<inter> assum(p, R) F \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cp \<Gamma> (Basic f) s" and a11:"c \<in> assum(p, R) F"
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof - 
      {
       have cp:"l!0=(Basic f,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
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
         then have env_tran_right: "env_tran_right \<Gamma> l R \<and> Norm R" 
           using env_tran env_tran_right_def a2 unfolding env_tran_def by auto
         then have all_event:"\<forall>j. 0\<le>j \<and> j \<noteq> k \<and> Suc j < length l \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
           using a00 a11  only_one_component_tran_all_env_basic[of \<Gamma> l 0 f k R] env_tran_right cp len_l
           by fastforce
         then have before_k_all_evn:"\<forall>j. 0\<le>j \<and> j < k  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
               using a00 a11  by fastforce
         then have k_basic:"fst(l!k) = Basic f \<and> snd (l!k) \<in> Normal ` (p)" 
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
         obtain s' s'' where ss:"snd (l!k) = Normal s' \<and> s' \<in> (p) \<and>  snd (l!(Suc k)) = Normal s'' \<and> s'' \<in> q"
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
           moreover have "fst (l!0) = Basic f" using cp by auto
           ultimately show ?thesis 
             using cp final_exist_component_tran_basic env_tran a2 by blast 
         qed
         then obtain k where k_comp_tran: "k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
           by auto
         then have all_event:"\<forall>j. 0\<le>j \<and> j \<noteq> k \<and> Suc j < length l \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
           using a2 only_one_component_tran_all_env_basic[of \<Gamma> l 0 f k R] env_tran_right cp len_l
           by fastforce
         then have before_k_all_evn:"\<forall>j. 0\<le>j \<and> j < k  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
               using k_comp_tran by fastforce
         then have k_basic:"fst(l!k) = Basic f \<and> snd (l!k) \<in> Normal ` (p)" 
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
         using  a2 last_l len_l cp env_tran_right a3 suc_k_skip_q assum k_comp_tran stability [of q R l "Suc k" "((length l) - 1)" _ \<Gamma>] 
           by fastforce                 
       } thus ?thesis by auto qed
       note res = conjI [OF concl concr]               
      }              
      thus ?thesis using c_prod unfolding comm_def by auto qed      
    } thus ?thesis by auto qed 
  } thus ?thesis by (simp add: com_validity_def[of \<Gamma>] com_cvalidity_def)
qed

subsection {* Spec Sound *}

lemma spec_skip:
   "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> c1=Skip"
proof -
  {fix s1 s2 c1
   assume "\<Gamma>\<turnstile>\<^sub>c(Spec r,s1)  \<rightarrow> ((c1,s2))"     
   then have "c1=Skip" using stepc_elim_cases(4) by force    
  } thus ?thesis by auto 
qed  


lemma no_comp_tran_before_i_spec:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Spec r" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "k\<le>j \<and> j < i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" and
         a4: "\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))" and
         a5: "env_tran_right \<Gamma> l rely \<and> Norm rely" 
   shows "P"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  spec_skip by blast
  thus ?thesis using  a0 a1 a2 a3 a4 a5 no_comp_tran_before_i by blast
qed

lemma only_one_component_tran_i_spec:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Spec r" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "k\<le>j \<and> j \<noteq> i \<and> Suc j < length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" and
         a4: "env_tran_right \<Gamma> l rely \<and> Norm rely"       
   shows "P"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  spec_skip by blast
  thus ?thesis using  a0 a1 a2 a3 a4 only_one_component_tran_i by blast
qed   

lemma only_one_component_tran_spec:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Spec r" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "k\<le>j \<and> j \<noteq> i \<and> Suc j < length l" and
         a4: "env_tran_right \<Gamma> l rely \<and> Norm rely"       
   shows "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  spec_skip by blast
  thus ?thesis using  a0 a1 a2 a3 a4 only_one_component_tran by blast
qed   

lemma only_one_component_tran_all_env_spec:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Spec r" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and         
         a3: "env_tran_right \<Gamma> l rely \<and> Norm rely"       
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  spec_skip by blast
  thus ?thesis using  a0 a1 a2 a3  only_one_component_tran by blast
qed   

lemma only_one_component_tran_all_not_comp_spec:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Spec r" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and         
         a3: "env_tran_right \<Gamma> l rely \<and> Norm rely"       
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  spec_skip by blast
  thus ?thesis using  a0 a1 a2 a3 only_one_component_tran_all_not_comp by blast
qed   

lemma final_exist_component_tran_spec:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
          a1: "fst (l!i) = Spec r" and               
          a2: "env_tran \<Gamma> q l R \<and> Norm R" and
          a3: "i\<le>j \<and> j < length l \<and> final (l!j)" 
  shows "\<exists>k. k\<ge>i \<and> k<j \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  spec_skip by blast
  thus ?thesis using  a0 a1 a2 a3 final_exist_component_tran by blast
qed   

lemma Spec_sound: 
       "p \<subseteq> {s. (\<forall>t. (s,t)\<in>r \<longrightarrow> t \<in> q) \<and> (\<exists>t. (s,t) \<in> r)} \<Longrightarrow>
       (\<forall>s t. s\<in>p  \<and> (s,t)\<in>r \<longrightarrow> (Normal s, Normal t) \<in> G) \<Longrightarrow>       
       Sta p R \<Longrightarrow>
       Sta q R \<Longrightarrow> Norm R \<Longrightarrow>      
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  (Spec r) sat [p, R, G, q,a]"
proof -  
 assume
    a0:"p \<subseteq> {s. (\<forall>t. (s,t)\<in>r \<longrightarrow> t \<in> q) \<and> (\<exists>t. (s,t) \<in> r)}" and
    a1:"(\<forall>s t. s\<in>p  \<and> (s,t)\<in>r \<longrightarrow> (Normal s,Normal t) \<in> G)" and
    a2:"Sta p R" and
    a3:"Sta q R" and 
    a4:"Norm R"
{
    fix s
    have "cp \<Gamma> (Spec r) s \<inter> assum(p, R) F \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cp \<Gamma> (Spec r) s" and a11:"c \<in> assum(p, R) F"
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof - 
      {
       have cp:"l!0=(Spec r,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
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
           using a00 a11 a4  only_one_component_tran_all_env_spec[of \<Gamma> l 0 r k R] env_tran_right cp len_l
           by fastforce
         then have before_k_all_evn:"\<forall>j. 0\<le>j \<and> j < k  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
               using a00 a11  by fastforce
         then have k_basic:"ck = Spec r \<and> sk \<in> Normal ` (p)" 
           using  cp a4 env_tran_right a2 assum a00 a11 stability[of p R l 0 k k \<Gamma>] tran_pair
           by force
         have suc_skip: "csk = Skip"
            using a0 a00 k_basic tran_pair spec_skip by blast
         obtain s' where ss:"sk = Normal s' \<and> s' \<in> (p)" 
           using k_basic by fastforce
         obtain s'' where suc_k_skip_q:"ssk = Normal s'' \<and> (s',s'')\<in>r "           
         proof -                    
           {from ss  obtain t where "ssk = Normal t" 
             using step_spec_skip_normal_normal[of \<Gamma>1 ck sk csk ssk r s'] 
                   k_basic tran_pair a0 suc_skip
             by blast           
           then obtain t where "ssk= Normal t" by fastforce
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
           moreover have "fst (l!0) = Spec r" using cp by auto
           ultimately show ?thesis 
             using cp final_exist_component_tran_spec env_tran a4 by blast 
         qed
         then obtain k  where k_comp_tran: "k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
           by auto
         then obtain ck sk csk ssk where tran_pair:
           "\<Gamma>1\<turnstile>\<^sub>c (ck,sk)  \<rightarrow> (csk, ssk) \<and> (ck = fst (l!k)) \<and> (sk = snd (l!k)) \<and> (csk = fst (l!(Suc k))) \<and> (ssk = snd (l!(Suc k)))" 
           using cp by fastforce
         then have all_event:"\<forall>j. 0\<le>j \<and> j \<noteq> k \<and> Suc j < length l \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
           using a4  k_comp_tran only_one_component_tran_all_env_spec[of \<Gamma> l 0 r k R] env_tran_right cp len_l
           by fastforce
         then have before_k_all_evn:"\<forall>j. 0\<le>j \<and> j < k  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
               using k_comp_tran by fastforce
         then have k_basic:"ck = Spec r \<and> sk \<in> Normal ` (p)" 
           using a4 cp env_tran_right a2 assum tran_pair k_comp_tran stability[of p R l 0 k k \<Gamma>] tran_pair
           by force
         have suc_skip: "csk = Skip"
            using a0  k_basic tran_pair spec_skip by blast
         have suc_k_skip_q:"ssk \<in> Normal ` q"           
         proof -         
           obtain s' where k_s: "sk =Normal s' \<and> s' \<in> (p)" 
             using k_basic by auto
           then obtain t where "ssk = Normal t" 
           using step_spec_skip_normal_normal[of \<Gamma>1 ck sk csk ssk r s'] k_basic tran_pair a0 suc_skip
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
         using l tran_pair suc_skip last_l len_l cp a4
               env_tran_right a3 suc_k_skip_q 
               assum k_comp_tran stability [of q R l "Suc k" "((length l) - 1)" _ \<Gamma>] 
         by (metis One_nat_def Suc_eq_plus1 Suc_leI Suc_mono diff_Suc_1 lessI list.size(4))                  
       } thus ?thesis by auto qed
       note res = conjI [OF concl concr]               
      }              
      thus ?thesis using c_prod unfolding comm_def by auto qed      
    } thus ?thesis by auto qed 
  } thus ?thesis by (simp add: com_validity_def[of \<Gamma>] com_cvalidity_def)
qed

subsection {* Await Sound *}

lemma await_skip:
   "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> c1=Skip \<or> (c1 = Throw \<and> (\<exists>s21. s2 =Normal s21 ))"
proof -
  {fix s1 s2 c1
   assume "\<Gamma>\<turnstile>\<^sub>c(Await b c,s1)  \<rightarrow> ((c1,s2))"     
   then have "c1=Skip \<or>  (c1 = Throw \<and> (\<exists>s21. s2 =Normal s21 ))" using stepc_elim_cases(8) by blast    
  } thus ?thesis by auto 
qed  

lemma no_comp_tran_before_i_await:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Await b c" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "k\<le>j \<and> j < i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" and
         a4: "\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))" and
         a5: "env_tran_right \<Gamma> l rely \<and> Norm rely" 
   shows "P"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow>  c1=Skip \<or> (c1 = Throw \<and> (\<exists>s21. s2 =Normal s21 ))" 
    using  await_skip by blast
  thus ?thesis using  a0 a1 a2 a3 a4 a5 no_comp_tran_before_i by blast
qed

lemma only_one_component_tran_i_await:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Await b c" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "k\<le>j \<and> j \<noteq> i \<and> Suc j < length l \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" and
         a4: "env_tran_right \<Gamma> l rely \<and> Norm rely"       
   shows "P"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)\<or>(c1 = Throw \<and> (\<exists>s21. s2 =Normal s21 ))" 
    using  await_skip by blast
  thus ?thesis using  a0 a1 a2 a3 a4 only_one_component_tran_i by blast
qed   

lemma only_one_component_tran_await:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Await b c" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "k\<le>j \<and> j \<noteq> i \<and> Suc j < length l" and
         a4: "env_tran_right \<Gamma> l rely \<and> Norm rely"       
   shows "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)\<or>(c1 = Throw \<and> (\<exists>s21. s2 =Normal s21 ))" 
    using  await_skip by blast
  thus ?thesis using  a0 a1 a2 a3 a4 only_one_component_tran by blast
qed   

lemma only_one_component_tran_all_env_await:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Await b c" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and         
         a3: "env_tran_right \<Gamma> l rely \<and> Norm rely"       
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)\<or>(c1 = Throw \<and> (\<exists>s21. s2 =Normal s21 ))" 
    using  await_skip by blast
  thus ?thesis using  a0 a1 a2 a3  only_one_component_tran by blast
qed   

lemma only_one_component_tran_all_not_comp_await:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Await b  c" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and         
         a3: "env_tran_right \<Gamma> l rely \<and> Norm rely"       
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)\<or>(c1 = Throw \<and> (\<exists>s21. s2 =Normal s21 ))" 
    using  await_skip by blast
  thus ?thesis using  a0 a1 a2 a3 only_one_component_tran_all_not_comp by blast
qed   

lemma final_exist_component_tran_await:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
          a1: "fst (l!i) = Await b c" and               
          a2: "env_tran \<Gamma> q l R \<and> Norm R" and
          a3: "i\<le>j \<and> j < length l \<and> final (l!j)" 
  shows "\<exists>k. k\<ge>i \<and> k<j \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)\<or>(c1 = Throw \<and> (\<exists>s21. s2 =Normal s21 ))" 
    using  await_skip by blast
  thus ?thesis using  a0 a1 a2 a3 final_exist_component_tran by blast
qed   

inductive_cases stepc_elim_cases_Await_Fault:
"\<Gamma>\<turnstile>\<^sub>c (Await b c, Normal s) \<rightarrow> (u,Fault f)"

lemma Await_sound: 
       "\<forall>V. \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
          (p \<inter> b \<inter> {V}) e 
          ({s. (Normal V, Normal s) \<in> G} \<inter> q),
          ({s. (Normal V, Normal s) \<in> G} \<inter> a) \<Longrightarrow>     
       Sta p R \<Longrightarrow> Sta q R \<Longrightarrow> Sta a R \<Longrightarrow> Norm R \<Longrightarrow>      
       \<Gamma>,\<Theta>\<Turnstile>\<^bsub>/F\<^esub> (Await b e) sat [p, R, G, q,a]"
proof -  
 assume
    a0: "\<forall>V. \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
          (p \<inter> b \<inter> {V}) e 
          ({s. (Normal V, Normal s) \<in> G} \<inter> q),
          ({s. (Normal V, Normal s) \<in> G} \<inter> a)" and
    a2:"Sta p R" and
    a3:"Sta q R" and
    a4:"Sta a R" and 
    a5:"Norm R"
{
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"
    have "cp \<Gamma> (Await b e) s \<inter> assum(p, R) F \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cp \<Gamma> (Await b e) s" and a11:"c \<in> assum(p, R) F"
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof - 
      {assume last_fault:"snd (last l) \<notin> Fault ` F"
       have cp:"l!0=(Await b e,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
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
         obtain ck sk csk ssk where tran_pair:
           "\<Gamma>1\<turnstile>\<^sub>c (ck,sk)  \<rightarrow> (csk, ssk) \<and> (ck = fst (l!k)) \<and> (sk = snd (l!k)) \<and> (csk = fst (l!(Suc k))) \<and> (ssk = snd (l!(Suc k)))" 
           using a11 by fastforce
         have len_l:"length l > 0" using cp using cptn.simps by blast 
         then obtain a1 l1 where l:"l=a1#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
         have last_l:"last l = l!(length l-1)"
           using last_length [of a1 l1] l by fastforce
         have env_tran:"env_tran \<Gamma> p l R" using assum env_tran_def cp by blast
         then have env_tran_right: "env_tran_right \<Gamma> l R" 
           using env_tran env_tran_right_def unfolding env_tran_def by auto
         then have all_event:"\<forall>j. 0\<le>j \<and> j \<noteq> k \<and> Suc j < length l \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
           using a5 a00 a11  only_one_component_tran_all_env_await[of \<Gamma> l 0 b e k R] env_tran_right cp len_l
           by fastforce
         then have before_k_all_evn:"\<forall>j. 0\<le>j \<and> j < k  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
               using a00 a11  by fastforce
         then obtain s' where k_basic:"ck = Await b e \<and> sk \<in> Normal ` (p) \<and> sk = Normal s'" 
           using a5 cp env_tran_right a2 assum a00 a11  stability[of p R l 0 k k \<Gamma>] tran_pair
           by force                 
         have suc_skip: "csk = Skip  \<or> (csk = Throw \<and> (\<exists>s1. ssk = Normal s1))"
            using a0 a00 k_basic tran_pair await_skip by blast
         have suc_k_skip_q:"ssk \<in> Normal ` ({s. (Normal s', Normal s) \<in> G} \<inter> q) \<or> 
                            ssk \<in> Normal ` ({s. (Normal s', Normal s) \<in> G} \<inter> a)"           
         proof -         
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
           have step_await:"\<Gamma>\<turnstile>\<^sub>c (Await b e,sk)  \<rightarrow> (csk, ssk)"
             using tran_pair cp k_basic by fastforce           
           then have s'_in_bp:"s'\<in> b \<and> s' \<in> p"  using k_basic stepc_Normal_elim_cases(8) by auto 
           then have "s' \<in> (p \<inter> b)"  by fastforce
           moreover have test:
            "\<exists>t. \<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>e,Normal s'\<rangle> \<Rightarrow> t \<and> 
             ((\<exists>t'. t =Abrupt t' \<and> ssk = Normal t') \<or>
             (\<forall>t'. t \<noteq> Abrupt t' \<and> ssk=t)) "
           proof -
             fix t 
             { assume "csk = Skip"
               then have step:"\<Gamma>\<turnstile>\<^sub>c (Await b e,Normal s')  \<rightarrow> (Skip, ssk)"
                 using step_await k_basic by fastforce
               have s'_b:"s'\<in>b" using s'_in_bp by fastforce
               note step = stepc_elim_cases_Await_skip[OF step]
               have h:"(s' \<in> b \<Longrightarrow> \<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>e,Normal s'\<rangle> \<Rightarrow> ssk \<Longrightarrow> \<forall>t'. ssk \<noteq> Abrupt t' \<Longrightarrow>
                      \<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>e,Normal s'\<rangle> \<Rightarrow> ssk \<and> (\<forall>t'. ssk \<noteq> Abrupt t'))" by auto
               have ?thesis 
                 using step[OF h] by fastforce
             } note left = this
             { assume "csk= Throw \<and> (\<exists>s1. ssk = Normal s1)"
               then obtain s1 where step:"csk= Throw \<and> ssk = Normal s1"
                 by fastforce
               then have step: "\<Gamma>\<turnstile>\<^sub>c (Await b e,Normal s')  \<rightarrow> (Throw, ssk)"
                 using step_await k_basic by fastforce
               have s'_b:"s'\<in>b" using s'_in_bp by fastforce
               note step = stepc_elim_cases_Await_throw[OF step]
               have h:"(\<And>t'. ssk = Normal t' \<Longrightarrow> s' \<in> b \<Longrightarrow> \<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>e,Normal s'\<rangle> \<Rightarrow> Abrupt t' \<Longrightarrow> 
                        \<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>e,Normal s'\<rangle> \<Rightarrow> Abrupt t' \<and>  ssk = Normal t')"
               by auto                
               have ?thesis using step[OF h] by blast 
             } thus ?thesis using suc_skip left by fastforce
           qed          
           then obtain t where e_step:"\<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>e,Normal s'\<rangle> \<Rightarrow> t \<and> 
             ((\<exists>t'. t =Abrupt t' \<and> ssk = Normal t') \<or>
             (\<forall>t'. t \<noteq> Abrupt t' \<and> ssk=t)) " by fastforce
           moreover have "t \<notin> Fault ` F" 
           proof -           
             {assume a10:"t \<in> Fault ` F"
             then obtain tf where "t=Fault tf \<and> tf\<in>F" by fastforce
             then have "ssk = Fault tf \<and> tf\<in>F" using e_step by fastforce
             also have "ssk \<notin> Fault  ` F" 
               using last_not_F[of \<Gamma> l F] last_fault cp tran_pair a00 by fastforce
             ultimately have False by auto
             } thus ?thesis by auto
           qed
           ultimately have t_q_a:"t \<in> Normal ` ({s. (Normal s', Normal s) \<in> G} \<inter>q) \<union> 
                                      Abrupt ` ({s. (Normal s', Normal s) \<in> G} \<inter> a)" 
             using e_auto unfolding valid_def by fastforce
           thus ?thesis using e_step t_q_a by blast                                                                        
         qed                                                                
         obtain s'' where ss:
           "sk = Normal s' \<and> s' \<in> (p) \<and>  ssk = Normal s'' 
            \<and> (s'' \<in> (({s. (Normal s', Normal s) \<in> G} \<inter> q)) \<or> 
               s''\<in> (({s. (Normal s', Normal s) \<in> G} \<inter> a)))"
           using suc_k_skip_q k_basic  by fastforce 
         then have "(snd(l!k), snd(l!(Suc k))) \<in> G"
           using a2 tran_pair by force
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
           moreover have "fst (l!0) = Await b e" using cp by auto
           ultimately show ?thesis 
             using a5 cp final_exist_component_tran_await env_tran by blast 
         qed
         then obtain k  where k_comp_tran: "k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
           by auto
         then obtain ck sk csk ssk where tran_pair:
           "\<Gamma>1\<turnstile>\<^sub>c (ck,sk)  \<rightarrow> (csk, ssk) \<and> (ck = fst (l!k)) \<and> (sk = snd (l!k)) \<and> (csk = fst (l!(Suc k))) \<and> (ssk = snd (l!(Suc k)))" 
           using cp by fastforce
         then have all_event:"\<forall>j. 0\<le>j \<and> j \<noteq> k \<and> Suc j < length l \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
           using  a5 k_comp_tran only_one_component_tran_all_env_await[of \<Gamma> l 0 b e k R] env_tran_right cp len_l
           by fastforce
         then have before_k_all_evn:"\<forall>j. 0\<le>j \<and> j < k  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
               using k_comp_tran by fastforce
         then obtain s' where k_basic:"ck = Await b e \<and> sk \<in> Normal ` (p) \<and> sk = Normal s'" 
           using a5  cp env_tran_right a2 assum tran_pair k_comp_tran stability[of p R l 0 k k \<Gamma>] tran_pair
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
                a5 assum k_comp_tran stability [of q R l "Suc k" "((length l) - 1)" _ \<Gamma>]         
               by (metis One_nat_def Suc_eq_plus1 Suc_leI Suc_mono diff_Suc_1 lessI list.size(4))
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
                 have f1: "Suc k < length l" using k_comp_tran len_l
                 by fastforce
                 have "env_tran_right \<Gamma>1 l R"
                   using cp env_tran_right by blast
                 then have "Suc k=length l -1" 
                   using f1  skip_fault_last[of \<Gamma>1 l "Suc k" ssk R] at 
                    a5 cp local.Fault prod.collapse tran_pair xstate.distinct(3) 
                   by metis
                 thus ?thesis using at last_l last_fault suck_fault tran_pair
                   by auto
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
              a5 assum k_comp_tran stability [of a R l "Suc k" "((length l) - 1)" _ \<Gamma>]        
           by (metis One_nat_def Suc_eq_plus1 Suc_leI Suc_mono diff_Suc_1 lessI list.size(4))           
         }
         ultimately have "fst (last l) = Skip \<and> 
                             snd ((last l)) \<in> Normal ` q \<or>
                            (fst (last l) = Throw \<and> snd (last l) \<in> Normal ` (a))"
         by blast                     
       } thus ?thesis by auto qed
       note res = conjI [OF concl concr]               
      }              
      thus ?thesis using c_prod unfolding comm_def by auto qed      
    } thus ?thesis by auto qed 
  } thus ?thesis by (simp add: com_validity_def[of \<Gamma>] com_cvalidity_def)     
qed

subsection {* If sound *}

lemma cptn_assum_induct:
assumes
  a0: "(\<Gamma>,l) \<in> (cp \<Gamma> c s) \<and> ((\<Gamma>,l) \<in> assum(p, R) F)" and
  a1: "k < length l \<and> l!k=(c1,Normal s') \<and> s' \<in> p1"
shows "(\<Gamma>,drop k l)\<in> ((cp \<Gamma> c1 (Normal s')) \<inter> assum(p1, R) F)"
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
    } thus "(\<Gamma>, drop k l) \<in> assum (p1, R) F" 
      using l unfolding assum_def by fastforce  
  qed  
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


lemma If_sound: 
      "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> b,  R, G, q,a] \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> b,  R, G, q,a] \<Longrightarrow>
       \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [p \<inter> (-b),  R, G, q,a] \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c2 sat [p \<inter> (-b),  R, G, q,a] \<Longrightarrow>      
       Sta p R \<Longrightarrow> (\<forall>s. (Normal s, Normal s) \<in> G) \<Longrightarrow>  Norm R \<Longrightarrow> 
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> (Cond b c1 c2) sat [p, R, G, q,a]"
proof -  
 assume
    a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> b,  R, G, q,a]" and
    a1:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [p \<inter> (-b), R, G, q,a]" and    
    a2: "\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> b, R, G, q,a]" and
    a3: "\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c2 sat [p \<inter> (-b), R, G, q,a]" and
    a4: "Sta p R" and
    a5: "(\<forall>s. (Normal s, Normal s) \<in> G)" and
    a6: "Norm R"    
  { 
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"
    then have a3:"\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c2 sat [p \<inter> (-b), R, G, q,a]" 
      using a3 com_cvalidity_def by fastforce 
    have a2:"\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> b, R, G, q,a]"
      using a2 all_call com_cvalidity_def by fastforce 
    have "cp \<Gamma> (Cond b c1 c2)  s \<inter> assum(p, R) F \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cp \<Gamma> (Cond b c1 c2) s" and a11:"c \<in> assum(p, R) F"
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof - 
      {assume l_f:"snd (last l) \<notin> Fault ` F"  
       
       have cp:"l!0=((Cond b c1 c2),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
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
           using a6 pair_j before_k_all_evnt cp env_tran_right a4 assum a00 stability[of p R l 0 j j \<Gamma>]
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
             moreover then have "cp \<Gamma> csj ssj \<inter> assum((p \<inter> b), R) F \<subseteq> comm(G, (q,a)) F"
               using a2 com_validity_def cj by blast             
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
               using l_suc j_length a10 a11 \<Gamma>1  ssj_normal_s
                     cptn_assum_induct[of \<Gamma> l "(LanguageCon.com.Cond b c1 c2)" s p R F "Suc j" c1 s' "(p \<inter> b)"]
               by blast                         
             show ?thesis 
               using l_k drop_comm a00 a21  a10 \<Gamma>1 l_f  
               cptn_comm_induct[of \<Gamma> l "(LanguageCon.com.Cond b c1 c2)" s _ "Suc j" G q a F k]
               by fastforce                       
           next
             assume a000:"s'\<notin>b"
              then have cj:"csj=c2" using k_basic pair_j ss 
                  by (metis (no_types) fst_conv stepc_Normal_elim_cases(6))
             moreover have p1:"s' \<in> (p \<inter> (-b))" using a000 ss by fastforce
             moreover then have "cp \<Gamma> csj ssj \<inter> assum((p \<inter> (-b)), R) F \<subseteq> comm(G, (q,a)) F"
               using a3 com_validity_def cj by blast             
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
               using l_suc j_length a10 a11 \<Gamma>1  ssj_normal_s
                     cptn_assum_induct[of \<Gamma> l "(LanguageCon.com.Cond b c1 c2)" s p R F "Suc j" c2 s' "(p \<inter> (-b))"]
               by fastforce             
             show ?thesis 
             using l_k drop_comm a00 a21 a6 a10 \<Gamma>1 l_f
             cptn_comm_induct[of \<Gamma> l "(LanguageCon.com.Cond b c1 c2)" s _ "Suc j" G q a F k]
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
             using cp final_exist_component_tran_final env_tran_right final_0 a6 
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
         using a6 pair_j before_k_all_evnt cp env_tran_right a4 assum a00 stability[of p R l 0 j j \<Gamma>]
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
         moreover then have "cp \<Gamma> csj ssj \<inter> assum((p \<inter> b), R) F \<subseteq> comm(G, (q,a)) F"
           using a2 com_validity_def cj by blast         
         ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
           using l_suc j_length a10 a11 \<Gamma>1  ssj_normal_s
                 cptn_assum_induct[of \<Gamma> l "(LanguageCon.com.Cond b c1 c2)" s p R F "Suc j" c1 s' "(p \<inter> b)"]
           by blast                   
         thus ?thesis       
           using j_length drop_comm   a10 \<Gamma>1  cptn_comm_induct[of \<Gamma> l "(LanguageCon.com.Cond b c1 c2)" s _ "Suc j" G q a F "Suc j"] valid not_fault 
           by blast
       next
         assume a000:"s'\<notin>b"
         then have cj:"csj=c2" using k_basic pair_j ss 
                  by (metis (no_types) fst_conv stepc_Normal_elim_cases(6))
         moreover have p1:"s'\<in>(p \<inter> (-b))" using a000 ss by blast 
         moreover then have "cp \<Gamma> csj ssj \<inter> assum((p \<inter> (-b)), R) F \<subseteq> comm(G, (q,a)) F"
           using a3 com_validity_def cj by blast         
         ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
           using l_suc j_length a10 a11 \<Gamma>1  ssj_normal_s
                 cptn_assum_induct[of \<Gamma> l "(LanguageCon.com.Cond b c1 c2)" s p R F "Suc j" c2 s' "(p \<inter> (-b))"]
           by blast                   
         thus ?thesis       
           using j_length drop_comm a10 \<Gamma>1  cptn_comm_induct[of \<Gamma> l "(LanguageCon.com.Cond b c1 c2)" s _ "Suc j" G q a F "Suc j"] valid not_fault 
           by blast
       qed
       } thus ?thesis using l_f by fastforce qed
       note res = conjI [OF concl concr]              
      }             
      thus ?thesis using c_prod  unfolding comm_def by auto  qed      
    } thus ?thesis by auto qed 
  } thus ?thesis by (simp add: com_validity_def[of \<Gamma>] com_cvalidity_def) 
qed


lemma Asm_sound:
   "(c, p, R, G, q, a) \<in> \<Theta> \<Longrightarrow>    
    \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]
   "
proof -
  assume
   a0:"(c, p, R, G, q, a) \<in> \<Theta>"    
   { fix s
     assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p,  R, G, q,a]"
     then have "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]" using a0 by auto
   } thus ?thesis unfolding com_cvalidity_def by auto
qed

lemma Call_sound: 
      "f \<in> dom \<Gamma> \<Longrightarrow>      
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> (the (\<Gamma> f)) sat [p, R, G, q,a] \<Longrightarrow>         
       Sta p R \<Longrightarrow> (\<forall>s. (Normal s,Normal s) \<in> G) \<Longrightarrow> Norm R \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> (Call f) sat [p, R, G, q,a]"
proof -  
  assume
    a0:"f \<in> dom \<Gamma>" and
    a2:"\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> (the (\<Gamma> f)) sat [p, R, G, q,a]" and        
    a3: "Sta p R" and
    a4: "(\<forall>s. (Normal s, Normal s) \<in> G)" and
    a5: "Norm R"      
  obtain bdy where a0:"\<Gamma> f = Some bdy" using a0 by auto
  { 
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p,  R, G, q,a]"  
    then have a2:"\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> bdy sat [p, R, G, q,a]" 
      using a0 a2 com_cvalidity_def by fastforce
    have "cp \<Gamma> (Call f)  s \<inter> assum(p, R) F \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cp \<Gamma> (Call f) s" and a11:"c \<in> assum(p, R) F"
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof - 
      {assume l_f:"snd (last l) \<notin> Fault ` F"       
        have cp:"l!0=((Call f),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
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
           using  a5 pair_j before_k_all_evnt cp env_tran_right a3 assum a00 stability[of p R l 0 j j \<Gamma>]
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
             moreover then have "cp \<Gamma> csj ssj \<inter> assum(p, R) F \<subseteq> comm(G, (q,a)) F"
               using a2 com_validity_def cj by blast
             moreover then have "l!(Suc j) = (csj, Normal s')" 
               using before_k_all_evnt pair_j cj ssj_normal_s
               by fastforce
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
               using  j_length a10 a11 \<Gamma>1  ssj_normal_s
                     cptn_assum_induct[of \<Gamma> l "Call f" s p R F "Suc j" bdy s' p]
               by blast                         
             then show ?thesis 
             using a00 a21 a10 \<Gamma>1  j_k j_length l_f
             cptn_comm_induct[of \<Gamma> l "Call f" s _ "Suc j" G q a F k ]
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
           moreover have "fst (l!0) = Call f" using cp by auto
           ultimately show ?thesis 
             using a5 cp final_exist_component_tran_final env_tran_right final_0 
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
              using a5 pair_j before_k_all_evnt cp env_tran_right a3 assum a00 stability[of p R l 0 j j \<Gamma>]
              by force
            then obtain s' where ss:"sj = Normal s' \<and> s'\<in> (p)" by auto 
            then have ssj_normal_s:"ssj = Normal s'" 
              using before_k_all_evnt k_basic pair_j a0 
              by (metis not_None_eq snd_conv stepc_Normal_elim_cases(9))
            have cj:"csj=bdy" using k_basic pair_j ss a0
              by (metis fst_conv option.distinct(1) option.sel stepc_Normal_elim_cases(9))                
            moreover have p1:"s'\<in>p" using ss by blast 
            moreover then have "cp \<Gamma> csj ssj \<inter> assum(p, R) F \<subseteq> comm(G, (q,a)) F"
              using a2 com_validity_def cj by blast
            moreover then have "l!(Suc j) = (csj, Normal s')" 
              using before_k_all_evnt pair_j cj ssj_normal_s
              by fastforce
            ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
              using  j_length a10 a11 \<Gamma>1  ssj_normal_s
              cptn_assum_induct[of \<Gamma> l "Call f" s p R F "Suc j" bdy s' p]
              by blast    
            thus ?thesis       
              using j_length l_f drop_comm a10 \<Gamma>1 cptn_comm_induct[of \<Gamma> l "Call f" s _ "Suc j" G q a F "Suc j"] valid  
              by blast
           qed
         } thus ?thesis by auto 
         qed
       note res = conjI [OF concl concr]}               
       thus ?thesis using  c_prod unfolding comm_def by force qed      
    } thus ?thesis by auto qed 
  } thus ?thesis by (simp add: com_validity_def[of \<Gamma>] com_cvalidity_def) 
qed

fun n_calls_cptn:: "('s,'p,'f) confs \<Rightarrow> nat"
where
"n_calls_cptn (\<Gamma>,[]) = 0"
|"n_calls_cptn (\<Gamma>,[a0]) = 0"
|"n_calls_cptn (\<Gamma>,[a0,a1]) = 0"
|"n_calls_cptn (\<Gamma>,a0#a1#l) = (if (\<exists>p. redex (fst a0) = Call p \<and> 
                                      redex (fst a1) = the (\<Gamma> p)) then
                                (n_calls_cptn (\<Gamma>,(a1#l))) + 1
                              else n_calls_cptn (\<Gamma>,(a1#l)))"

definition cptns_sat::"('s,'p,'f) body \<Rightarrow>  'f set \<Rightarrow> ('s,'p,'f) com \<Rightarrow> 
    's set \<Rightarrow> (('s,'f) tran) set \<Rightarrow>  (('s,'f) tran) set \<Rightarrow>  
    's set \<Rightarrow>  's set \<Rightarrow> (('s,'p,'f) confs) set"
where 
"cptns_sat \<Gamma> F Pr p R G q a \<equiv> 
  {cf. \<exists>s. cf \<in> (cp \<Gamma> Pr s \<inter> assum(p, R) F) \<and>
       (cp \<Gamma> Pr s \<inter> assum(p, R) F \<subseteq> comm(G, (q,a)) F) 
                               }"

definition max_calls_cptn_sat::"('s,'p,'f) body \<Rightarrow>  'f set \<Rightarrow> ('s,'p,'f) com \<Rightarrow> 
    's set \<Rightarrow> (('s,'f) tran) set \<Rightarrow>  (('s,'f) tran) set \<Rightarrow>  
    's set \<Rightarrow>  's set \<Rightarrow> nat"
where
"max_calls_cptn_sat \<Gamma> F Pr p R G q a \<equiv> 
  if (cptns_sat  \<Gamma> F Pr p R G q a) = {} then 0
  else
      (SOME n.
          (\<forall>n1 \<in> (n_calls_cptn ` (cptns_sat  \<Gamma> F Pr p R G q a)). 
            n1\<le>n))
"

definition calls_cptn_spec::
   "('s,'p,'f) body \<Rightarrow> 'f set \<Rightarrow> ('s, 'p, 'f) sextuple set \<Rightarrow> nat set"
where
"calls_cptn_spec \<Gamma> F \<Theta> \<equiv> 
  {n. \<forall>(Pr,p,R,G,q,a)\<in>\<Theta>. n \<in> (n_calls_cptn ` (cptns_sat  \<Gamma> F (Call Pr) p R G q a)) }
"

definition max_calls_cptn_spec::
  "('s,'p,'f) body \<Rightarrow>  'f set \<Rightarrow> ('s, 'p, 'f) sextuple set \<Rightarrow> nat "
where
"max_calls_cptn_spec \<Gamma> F \<Theta> \<equiv> 
  if (calls_cptn_spec  \<Gamma> F \<Theta>) = {} then 0
  else
    (SOME n. 
      (\<forall>n1 \<in> (calls_cptn_spec  \<Gamma> F \<Theta>). 
        n1\<le>n))
"

definition max_calls_cptn_spec_sat::
"('s,'p,'f) body \<Rightarrow>  'f set \<Rightarrow> ('s, 'p, 'f) sextuple set \<Rightarrow>
 ('s,'p,'f) com \<Rightarrow> 
    's set \<Rightarrow> (('s,'f) tran) set \<Rightarrow>  (('s,'f) tran) set \<Rightarrow>  
    's set \<Rightarrow>  's set \<Rightarrow> nat"
where
"max_calls_cptn_spec_sat  \<Gamma> F \<Theta>  Pr p R G q a \<equiv>
    if (max_calls_cptn_sat \<Gamma> F Pr p R G q a) \<ge> (max_calls_cptn_spec \<Gamma> F \<Theta>) then
       (max_calls_cptn_sat \<Gamma> F Pr p R G q a)
    else (max_calls_cptn_spec \<Gamma> F \<Theta>)
"


lemma CallRec_sound1:
    "(c, p, R, G, q, a) \<in> Specs \<Longrightarrow>
     \<forall>(c, p, R, G, q, a)\<in>Specs.
       c \<in> dom \<Gamma> \<and>
       Sta p R \<and>  (\<forall>s. (Normal s,Normal s) \<in> G) \<and> Norm R \<and>      
       \<Gamma>,\<Theta> \<union> Specs \<turnstile>\<^bsub>/F\<^esub> the (\<Gamma> c) sat [p, R, G, q,a] \<and> 
       \<Gamma>,\<Theta> \<union> Specs \<Turnstile>\<^bsub>/F\<^esub> the (\<Gamma> c) sat [p,R, G, q,a] \<Longrightarrow>
    Sta p R \<Longrightarrow> (\<forall>s. (Normal s,Normal s) \<in> G) \<Longrightarrow> Norm R \<Longrightarrow>
     \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]"
proof -
  assume a0: "(c, p, R, G, q, a) \<in> Specs" and
     a1: 
    "\<forall>(c, p, R, G, q, a)\<in>Specs.
       c \<in> dom \<Gamma> \<and> Sta p R \<and>  (\<forall>s. (Normal s,Normal s) \<in> G) \<and> Norm R \<and>  
       \<Gamma>,\<Theta> \<union> Specs \<turnstile>\<^bsub>/F\<^esub> the (\<Gamma> c) sat [p, R, G, q,a] \<and> 
       \<Gamma>,\<Theta> \<union> Specs \<Turnstile>\<^bsub>/F\<^esub> the (\<Gamma> c) sat [p,R, G, q,a]"
  then have a1': "c \<in> dom \<Gamma>"  and       
       a1'': "\<Gamma>,\<Theta> \<union> Specs \<Turnstile>\<^bsub>/F\<^esub> the (\<Gamma> c) sat [p,R, G, q,a]" using a0 by auto 
    from a1 have 
      valid_body:
      "\<forall>(c, p, R, G, q, a)\<in>Specs.
       c \<in> dom \<Gamma> \<and>  Sta p R \<and>  (\<forall>s. (Normal s,Normal s) \<in> G) \<and> Norm R \<and>       
       \<Gamma>,\<Theta> \<union> Specs \<Turnstile>\<^bsub>/F\<^esub> the (\<Gamma> c) sat [p,R, G, q,a]" by fastforce
  assume a5: "Sta p R" and
         a6: "(\<forall>s. (Normal s,Normal s) \<in> G)" and
         a7: "Norm R"  
  obtain bdy where \<Gamma>bdy:"\<Gamma> c = Some bdy" using a1' by auto
  have theta_specs: 
         "\<forall>(c, p, R, G, q, a)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a] \<Longrightarrow>
          \<forall>(c, p, R, G, q, a)\<in>Specs. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]"
  proof -
    assume a00:"\<forall>(c, p, R, G, q, a)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]"
    { 
       fix c1 p1 R1 G1 q1 a1
       assume a001:"(c1, p1, R1, G1, q1, a1)\<in>Specs"       
       then have "c1 \<in> dom \<Gamma> \<and> Sta p1 R1 \<and>  (\<forall>s. (Normal s,Normal s) \<in> G1) \<and> Norm R1 \<and>  
          \<Gamma>,\<Theta> \<union> Specs \<Turnstile>\<^bsub>/F\<^esub> the (\<Gamma> c1) sat [p1,R1, G1, q1,a1]" 
         using valid_body by fastforce
       then have "\<Gamma>,\<Theta> \<union> Specs \<Turnstile>\<^bsub>/F\<^esub> Call c1 sat [p1,R1, G1, q1,a1]"
         using Call_sound[of c1 \<Gamma> "\<Theta> \<union> Specs" F p1 R1 G1 q1 a1] a5 a6 a7
         by fastforce
       {
          fix s
          have "cp \<Gamma> (LanguageCon.com.Call c1) s \<inter> assum (p1, R1) F \<subseteq> comm (G1, q1, a1) F"
          proof -
          { 
            fix c
            assume a10:"c \<in> cp \<Gamma> (Call c1) s" and a11:"c\<in> assum(p1,R1) F"
            obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
            obtain n where h:"n_calls_cptn (\<Gamma>1,l) = n" by auto
            then have "c \<in> comm(G1, (q1,a1)) F" using a10 a11 
            proof (induct n arbitrary: l s p1 c)
              case 0 thus ?case sorry
            next
              case (Suc n) thus ?case sorry
            qed
          } thus ?thesis by auto qed
       }  
       then have "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Call c1 sat [p1,R1, G1, q1,a1]"
         unfolding com_validity_def by auto
          
    } thus ?thesis by auto
  qed
  then show ?thesis using a0 unfolding com_cvalidity_def by auto     
qed


lemma CallRec_sound:
    "(c, p, R, G, q, a) \<in> Specs \<Longrightarrow>
     \<forall>(c, p, R, G, q, a)\<in>Specs.
       c \<in> dom \<Gamma> \<and>
       Sta p R \<and>  (\<forall>s. (Normal s,Normal s) \<in> G) \<and> Norm R \<and>      
       \<Gamma>,\<Theta> \<union> Specs \<turnstile>\<^bsub>/F\<^esub> the (\<Gamma> c) sat [p, R, G, q,a] \<and> 
       \<Gamma>,\<Theta> \<union> Specs \<Turnstile>\<^bsub>/F\<^esub> the (\<Gamma> c) sat [p,R, G, q,a] \<Longrightarrow>
    Sta p R \<Longrightarrow> (\<forall>s. (Normal s,Normal s) \<in> G) \<Longrightarrow> Norm R \<Longrightarrow>
     \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]"
proof -
  assume a0: "(c, p, R, G, q, a) \<in> Specs" and
     a1: 
    "\<forall>(c, p, R, G, q, a)\<in>Specs.
       c \<in> dom \<Gamma> \<and> Sta p R \<and>  (\<forall>s. (Normal s,Normal s) \<in> G) \<and> Norm R \<and>  
       \<Gamma>,\<Theta> \<union> Specs \<turnstile>\<^bsub>/F\<^esub> the (\<Gamma> c) sat [p, R, G, q,a] \<and> 
       \<Gamma>,\<Theta> \<union> Specs \<Turnstile>\<^bsub>/F\<^esub> the (\<Gamma> c) sat [p,R, G, q,a]"
  then have a1': "c \<in> dom \<Gamma>"  and       
       a1'': "\<Gamma>,\<Theta> \<union> Specs \<Turnstile>\<^bsub>/F\<^esub> the (\<Gamma> c) sat [p,R, G, q,a]" using a0 by auto 
    from a1 have 
      valid_body:
      "\<forall>(c, p, R, G, q, a)\<in>Specs.
       c \<in> dom \<Gamma> \<and>  Sta p R \<and>  (\<forall>s. (Normal s,Normal s) \<in> G) \<and> Norm R \<and>       
       \<Gamma>,\<Theta> \<union> Specs \<Turnstile>\<^bsub>/F\<^esub> the (\<Gamma> c) sat [p,R, G, q,a]" by fastforce
  assume a5: "Sta p R" and
         a6: "(\<forall>s. (Normal s,Normal s) \<in> G)" and
         a7: "Norm R"  
  obtain bdy where \<Gamma>bdy:"\<Gamma> c = Some bdy" using a1' by auto
  have theta_specs: 
         "\<forall>(c, p, R, G, q, a)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a] \<Longrightarrow>
          \<forall>(c, p, R, G, q, a)\<in>Specs. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]"
  proof -
    assume a00:"\<forall>(c, p, R, G, q, a)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]"
    { 
       fix c1 p1 R1 G1 q1 a1
       assume "(c1, p1, R1, G1, q1, a1)\<in>Specs"
       then have "c1 \<in> dom \<Gamma> \<and> Sta p1 R1 \<and>  (\<forall>s. (Normal s,Normal s) \<in> G1) \<and> Norm R1 \<and>  
          \<Gamma>,\<Theta> \<union> Specs \<Turnstile>\<^bsub>/F\<^esub> the (\<Gamma> c1) sat [p1,R1, G1, q1,a1]" 
         using valid_body by fastforce
       then have "\<Gamma>,\<Theta> \<union> Specs \<Turnstile>\<^bsub>/F\<^esub> Call c1 sat [p1,R1, G1, q1,a1]"
         using Call_sound[of c1 \<Gamma> "\<Theta> \<union> Specs" F p1 R1 G1 q1 a1] a5 a6 a7
         by fastforce       
       then have "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Call c1 sat [p1,R1, G1, q1,a1]" 
         unfolding com_cvalidity_def using a00
            sorry
    } thus ?thesis by auto
  qed
  then show ?thesis using a0 unfolding com_cvalidity_def by auto     
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
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Seq c1 c2) s) \<and> ((\<Gamma>,l1) \<in> assum(p, R) F)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift c2) l2"  
shows
  "((\<Gamma>,l2) \<in> assum(p, R) F)"
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
    } thus "(\<Gamma>, l2) \<in> assum (p, R) F" 
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

lemma Seq_sound1: 
assumes
  a0:"(\<Gamma>,x)\<in>cptn_mod" and
  a1:"x!0 = ((Seq P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"\<not> final (last x)" and
  a4:"env_tran_right \<Gamma> x rely \<and> Norm rely"
shows
  "\<exists>xs. (\<Gamma>,xs) \<in> cp \<Gamma> P s \<and> x = map (lift Q) xs"
using a0 a1 a2 a3 a4
proof (induct arbitrary: P s)
  case (CptnModOne \<Gamma> C s1)
  then have "(\<Gamma>, [(P,s)]) \<in> cp \<Gamma> P s \<and> [(C, s1)] = map (lift Q) [(P,s)]"
    unfolding cp_def lift_def  by (simp add: cptn.CptnOne) 
  thus ?case by fastforce
next
  case (CptnModEnv \<Gamma> C s1 t1 xsa)
  then have C:"C=Seq P Q" unfolding lift_def by fastforce
  have "\<exists>xs. (\<Gamma>, xs) \<in> cp \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift Q) xs"
  proof -
     have "((C, t1) # xsa) ! 0 = (LanguageCon.com.Seq P Q, t1)" using C by auto
     moreover have "\<forall>i<length ((C, t1) # xsa). fst (((C, t1) # xsa) ! i) \<noteq> Q"
       using CptnModEnv(5) by fastforce
     moreover have "\<not> SmallStepCon.final (last ((C, t1) # xsa))" using CptnModEnv(6) 
       by fastforce
     ultimately show ?thesis
       using CptnModEnv(3) CptnModEnv(7) env_tran_tail by blast     
  qed 
  then obtain xs where hi:"(\<Gamma>, xs) \<in> cp \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift Q) xs"
    by fastforce
  have s1_s:"s1=s" using  CptnModEnv unfolding cp_def by auto
  obtain xsa' where xs:"xs=((P,t1)#xsa') \<and> (\<Gamma>,((P,t1)#xsa'))\<in>cptn \<and> (C, t1) # xsa = map (lift Q) ((P,t1)#xsa')" 
    using hi  unfolding cp_def by fastforce
  
  have env_tran:"\<Gamma>\<turnstile>\<^sub>c(P,s1) \<rightarrow>\<^sub>e (P,t1)" using CptnModEnv Seq_env_P by (metis fst_conv nth_Cons_0)  
  then have "(\<Gamma>,(P,s1)#(P,t1)#xsa')\<in>cptn" using xs env_tran CptnEnv by fastforce  
  then have "(\<Gamma>,(P,s1)#(P,t1)#xsa') \<in> cp \<Gamma> P s" 
    using cp_def s1_s by fastforce
  moreover have "(C,s1)#(C, t1) # xsa = map (lift Q) ((P,s1)#(P,t1)#xsa')"
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
  then have a1:"LanguageCon.com.Seq P Q = LanguageCon.com.Seq P0 P1"
    by fastforce  
  have f1: "sa = s"
    using CptnModSeq1.prems(1) by force
  have f2: "P = P0 \<and> Q = P1" using a1 by auto
  have "(\<Gamma>, (P0, sa) # xsa) \<in> cptn"
    by (metis CptnModSeq1.hyps(1) cptn_eq_cptn_mod_set)
  hence "(\<Gamma>, (P0, sa) # xsa) \<in> cp \<Gamma> P s"
    using f2 f1 by (simp add: cp_def)
  thus ?case
    using Cons_lift CptnModSeq1.hyps(3) a1 by blast   
next
  case (CptnModSeq2 \<Gamma> P0 sa xsa P1 ys zs) 
  then have "P0 = P \<and> P1 = Q" by auto
  then obtain i where zs:"fst (zs!i) = Q \<and> (i< (length zs))" using CptnModSeq2
    by (metis (no_types, lifting) add_diff_cancel_left' fst_conv length_Cons length_append nth_append_length zero_less_Suc zero_less_diff)    
  then have "Suc i< length ((Seq P0 P1,sa)#zs)" by fastforce
  then have "fst (((Seq P0 P1, sa) # zs)!Suc i) = Q" using zs by fastforce    
  thus ?case using CptnModSeq2(8) zs by auto
next
  case (CptnModSeq3 \<Gamma> P1 sa xsa s' ys zs Q1)
  have "final (last ((LanguageCon.com.Throw, Normal s')# ys))"
  proof -
    have cptn:"(\<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn" 
      using CptnModSeq3(5) by (simp add: cptn_eq_cptn_mod_set)
    moreover have throw_0:"((LanguageCon.com.Throw, Normal s') # ys)!0 = (Throw, Normal s') \<and> 0 < length((LanguageCon.com.Throw, Normal s') # ys)"
      by force         
    moreover have last:"last ((LanguageCon.com.Throw, Normal s') # ys) = ((LanguageCon.com.Throw, Normal s') # ys)!((length ((LanguageCon.com.Throw, Normal s') # ys)) - 1)"
      using last_conv_nth by auto
    moreover have env_tran:"env_tran_right \<Gamma> ((LanguageCon.com.Throw, Normal s') # ys) rely" 
      using  CptnModSeq3(11)  CptnModSeq3(7) env_tran_subl env_tran_tail by blast           
    ultimately obtain st' where "fst (last ((LanguageCon.com.Throw, Normal s') # ys)) = Throw \<and>        
                     snd (last ((LanguageCon.com.Throw, Normal s') # ys)) = Normal st'" 
    using CptnModSeq3(11) zero_throw_all_throw[of \<Gamma> "((Throw, Normal s') # ys)" "s'" "(length ((Throw, Normal s') # ys))-1"]
      by fastforce 
    thus ?thesis using CptnModSeq3(10) final_def by blast
  qed
  thus ?case using CptnModSeq3(10) CptnModSeq3(7)
    by force
qed (auto)

lemma Seq_sound2: 
assumes
  a0:"(\<Gamma>,x)\<in>cptn_mod" and
  a1:"x!0 = ((Seq P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"fst (last x) = Throw \<and> snd (last x) = Normal s'" and
  a4:"env_tran_right \<Gamma> x rely \<and> Norm rely"
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
    have "\<forall>c p. fst (case p of (ca::('s, 'a, 'd) LanguageCon.com, x::('s, 'd) xstate) \<Rightarrow> (LanguageCon.com.Seq ca c, x)) = LanguageCon.com.Seq (fst p) c"
      by simp
    then have "[] = xsa"
      using CptnModSeq1(6) CptnModSeq1(3)
      by (metis (no_types) LanguageCon.com.distinct(71) fst_conv last.simps last_map lift_def)
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

lemma Seq_sound3: 
assumes
  a0:"(\<Gamma>,x)\<in>cptn" and
  a1:"x!0 = ((Seq P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"fst(last x) = Skip" and
  a4:"env_tran_right \<Gamma> x rely \<and> Norm rely"
shows
  "False"
using a0 a1 a2 a3 a4
proof (induct arbitrary: P s)
  case (CptnOne \<Gamma> C s1) thus ?case by auto
next
  case (CptnEnv \<Gamma> C st t xsa) 
    thus ?case
    proof -
      have f1: "env_tran_right \<Gamma> ((C, t) # xsa) rely \<and> Norm rely"
        using CptnEnv.prems(4) env_tran_tail by blast
      have "LanguageCon.com.Seq P Q = C"
        using CptnEnv.prems(1) by auto
      then show ?thesis
        using f1 CptnEnv.hyps(3) CptnEnv.prems(2) CptnEnv.prems(3) by moura
    qed
next
  next
  case (CptnComp \<Gamma> C st C' st' xsa)
  then have c_seq:"C = (Seq P Q) \<and> st = s" by force
  from CptnComp show ?case proof(cases)
    case (Seqc P1 P1' P2) thus ?thesis
    proof -
      have f1: "env_tran_right \<Gamma> ((C', st') # xsa) rely \<and> Norm rely"
        using CptnComp.prems(4) env_tran_tail by blast
      have "Q = P2"
        using c_seq local.Seqc(1) by blast
      then show ?thesis
        using f1 CptnComp.hyps(3) CptnComp.prems(2) CptnComp.prems(3) local.Seqc(2) by moura
    qed
  next
    case  (SeqSkipc) thus ?thesis
    proof -
      have "LanguageCon.com.Seq LanguageCon.com.Skip C' = LanguageCon.com.Seq P Q"
        using c_seq local.SeqSkipc(1) by fastforce
      then have "fst (((C, st) # (C', st') # xsa) ! Suc 0) = Q"
        by simp
      then show ?thesis
        using CptnComp.prems(2) by force
    qed     
  next
    case (SeqThrowc C2 s') thus ?thesis
    proof -
      have f1: "((C', st') # xsa) ! 0 = (LanguageCon.com.Throw, Normal s')"
        by (simp add: local.SeqThrowc(3) local.SeqThrowc(4))
      have "fst (((C', st') # xsa) ! length xsa) \<noteq> LanguageCon.com.Throw"
        by (metis (no_types) CptnComp.prems(3) LanguageCon.com.simps(28) last.simps last_length list.simps(3))
      then show ?thesis
        using f1 by (metis CptnComp.hyps(2) CptnComp.prems(4) env_tran_tail fst_conv length_Cons lessI snd_conv zero_throw_all_throw)
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


lemma Seq_sound4: 
assumes
  a0:"(\<Gamma>,x)\<in>cptn" and
  a1:"x!0 = ((Seq P Q),s)" and
  a2:"i<length x \<and> x!i=(Q,sj)" and
  a3:"\<forall>j<i. fst(x!j)\<noteq>Q" and 
  a4:"env_tran_right \<Gamma> x rely \<and> Norm rely"
shows
  "\<exists>xs ys. (\<Gamma>,xs) \<in> (cp \<Gamma> P s) \<and> (\<Gamma>,ys) \<in> (cp \<Gamma> Q (snd (xs!(i-1)))) \<and> x = (map (lift Q) xs)@ys"
using a0 a1 a2 a3 a4
proof (induct arbitrary: i sj P s) 
  case (CptnOne \<Gamma> P s) thus ?case
    by auto 
next
  case (CptnEnv \<Gamma> C st t xsa)    
  have a1:"Seq P Q \<noteq> Q" by simp    
  then have C_seq:"C=(Seq P Q)" using CptnEnv by fastforce
  then have "fst(((C, st) # (C, t) # xsa)!0) \<noteq>Q" using CptnEnv a1 by auto
  moreover have  "fst(((C, st) # (C, t) # xsa)!1) \<noteq>Q" using CptnEnv a1 by auto
  moreover have "fst(((C, st) # (C, t) # xsa)!i) =Q" using CptnEnv by auto
  ultimately have i_suc: "i> (Suc 0)" using CptnEnv 
    by (metis Suc_eq_plus1 Suc_lessI add.left_neutral neq0_conv) 
  then obtain i' where i':"i=Suc i'" by (meson lessE) 
  then have i_minus:"i'=i-1" by auto
  have "((C, t) # xsa) ! 0 = ((Seq P Q), t)"
    using CptnEnv by auto 
  moreover have "i'< length ((C,t)#xsa) \<and> ((C,t)#xsa)!i' = (Q,sj)"
    using i' CptnEnv(5) by force
  moreover have "\<forall>j<i'. fst (((C, t) # xsa) ! j) \<noteq> Q"
    using i' CptnEnv(6) by force
  ultimately have hyp:"\<exists>xs ys.
     (\<Gamma>, xs) \<in> cp \<Gamma> P t \<and>
     (\<Gamma>, ys) \<in> cp \<Gamma> Q (snd (xs ! (i'-1))) \<and> (C, t) # xsa = map (lift Q) xs @ ys"
    using CptnEnv(3) env_tran_tail CptnEnv.prems(4) by blast 
  then obtain xs ys where xs_cp:"(\<Gamma>, xs) \<in> cp \<Gamma> P t \<and>
     (\<Gamma>, ys) \<in> cp \<Gamma> Q (snd (xs ! (i'-1))) \<and> (C, t) # xsa = map (lift Q) xs @ ys"
    by fast
  have "(\<Gamma>, (P,s)#xs) \<in> cp \<Gamma> P s"
  proof -
    have "xs!0 = (P,t)" 
      using xs_cp unfolding cp_def by blast
    moreover have "xs\<noteq>[]"
      using cp_def cptn.simps xs_cp by blast 
    ultimately obtain xs' where xs':"(\<Gamma>, (P,t)#xs') \<in> cptn \<and> xs=(P,t)#xs'" 
      using SmallStepCon.nth_tl xs_cp unfolding cp_def by force
    thus ?thesis using cp_def  cptn.CptnEnv
    proof -
      have "(LanguageCon.com.Seq P Q, s) = (C, st)"
        using CptnEnv.prems(1) by auto
      then have "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow>\<^sub>e (P, t)"
        using Seq_env_P CptnEnv(1) by blast
      then show ?thesis
        by (simp add:xs' cp_def cptn.CptnEnv)
    qed
  qed
  thus  ?case 
    using i_suc Cons_lift_append CptnEnv.prems(1) i' i_minus xs_cp
    by fastforce   
next
  case (CptnComp \<Gamma> C st C' st' xsa i)
  then have c_seq:"C = (Seq P Q) \<and> st = s" by force  
  from CptnComp show ?case proof(cases)
    case (Seqc P1 P1' P2)      
    then have C_seq:"C=(Seq P Q)" using CptnEnv CptnComp by fastforce    
    then have "fst(((C, st) # (C', st') # xsa)!0) \<noteq>Q" 
      using CptnComp by auto
    moreover have  "fst(((C, st) # (C', st') # xsa)!1) \<noteq>Q" 
      using  CptnComp Seqc by auto
    moreover have "fst(((C, st) # (C', st') # xsa)!i) =Q" 
      using CptnComp by auto
    ultimately have  i_gt0:"i> (Suc 0)" 
      by (metis Suc_eq_plus1 Suc_lessI add.left_neutral neq0_conv) 
    then obtain i' where i':"i=Suc i'" by (meson lessE) 
    then have i_minus:"i'=i-1" by auto
    have "((C', st') # xsa) ! 0 = ((Seq P1' Q), st')"
      using CptnComp Seqc by auto 
    moreover have "i'< length ((C',st')#xsa) \<and> ((C',st')#xsa)!i' = (Q,sj)"
      using i' CptnComp(5) by force
    moreover have "\<forall>j<i'. fst (((C', st') # xsa) ! j) \<noteq> Q"
    using i' CptnComp(6) by force   
    ultimately have "\<exists>xs ys.
       (\<Gamma>, xs) \<in> cp \<Gamma> P1' st' \<and>
       (\<Gamma>, ys) \<in> cp \<Gamma> Q (snd (xs ! (i'-1))) \<and> (C', st') # xsa = map (lift Q) xs @ ys"
    using CptnComp Seqc env_tran_tail CptnComp.prems(4) by blast   
    then obtain xs ys where xs_cp:
      "(\<Gamma>, xs) \<in> cp \<Gamma> P1' st' \<and>
       (\<Gamma>, ys) \<in> cp \<Gamma> Q (snd (xs ! (i'-1))) \<and> (C', st') # xsa = map (lift Q) xs @ ys"
      by fastforce
     have "(\<Gamma>, (P,s)#xs) \<in> cp \<Gamma> P s"        
     proof -
        have "xs!0 = (P1',st')" 
          using xs_cp unfolding cp_def by blast
        moreover have "xs\<noteq>[]"
          using cp_def cptn.simps xs_cp by blast 
        ultimately obtain xs' where xs':"(\<Gamma>, (P1',st')#xs') \<in> cptn \<and> xs=(P1',st')#xs'" 
          using SmallStepCon.nth_tl xs_cp unfolding cp_def by force
        thus ?thesis using cp_def  cptn.CptnEnv Seqc c_seq
              xs' cp_def cptn.CptnComp          
             by (simp add: cp_def cptn.CptnComp xs') 
     qed     
     thus ?thesis using Cons_lift c_seq i' xs_cp i_gt0 by fastforce
  next
    case (SeqSkipc) 
    with CptnComp have PC:"P=Skip \<and> C'=Q \<and> st=st' \<and> s=st" by fastforce
    then have "(\<Gamma>, [(Skip,st)]) \<in> cp \<Gamma> P s" unfolding cp_def using cptn.simps
      by fastforce
    moreover have "(\<Gamma>, (Q,st')#xsa) \<in> cp \<Gamma> Q st'" unfolding cp_def using CptnComp PC
      by fastforce
    moreover have "i=1" using CptnComp (4-6) PC
      by (metis One_nat_def fst_conv less_one linorder_neqE_nat local.SeqSkipc(1) nth_Cons_0 nth_Cons_Suc seq_not_eq2) 
    moreover have "[(Seq Skip Q, st)]  = map (lift Q) [(Skip,st)]" 
      unfolding lift_def by auto
    ultimately show ?thesis using PC SeqSkipc by fastforce
  next
    case (SeqThrowc C2 s') 
    with CptnComp have PC:"P=Throw \<and> C2=Q \<and> C'=Throw \<and> st=st' \<and> s=Normal s' \<and> st=s" by fastforce
    {assume a01:"Q=Throw"
     then have "(\<Gamma>, [(Throw, Normal s')]) \<in> cp \<Gamma> P s"
       using PC cptn.simps unfolding cp_def by fastforce
     moreover have "(\<Gamma>, (C', st') # xsa)\<in>cp \<Gamma> Q st' "
       using PC CptnComp unfolding cp_def a01 by fastforce
     moreover have "i=1" using CptnComp (4-6) PC a01
     proof -
       have "fst (((C, st) # (C', st') # xsa) ! Suc 0) = LanguageCon.com.Throw"
         using PC by force
       then have "\<not> Suc 0 < i"
         using local.CptnComp(6) a01 by blast 
       have "(LanguageCon.com.Throw, sj) \<noteq> (LanguageCon.com.Seq P Q, s)"
         by blast
       then have "i \<noteq> 0"
         using c_seq local.CptnComp(5) by force
       then have "Suc 0 = i"
         using \<open>\<not> Suc 0 < i\<close> by linarith
       then show ?thesis by auto    
     qed   
     moreover have "[(Seq Throw Q, st)]  = map (lift Q) [(Throw,st)]" 
      unfolding lift_def by auto
     ultimately have ?thesis  using PC SeqThrowc by fastforce 
    } note a1=this
    {assume a01:"Q\<noteq>Throw"
     have "\<forall>j< length ((C', st') # xsa) . fst (((C', st') # xsa) ! j) \<noteq> Q" 
     proof -
       have "\<forall>j<length ((C', st') # xsa). fst (((C', st') # xsa) ! j) = Throw"
       proof -
         have f1: "snd (((C', st') # xsa) ! 0) = Normal s'"
           using local.SeqThrowc(4) by auto
         have "fst (((C', st') # xsa) ! 0) = LanguageCon.com.Throw"
           using local.SeqThrowc(3) by auto
         then show ?thesis
           using f1 CptnComp.hyps(2) CptnComp.prems(4) env_tran_tail zero_throw_all_throw 
             by fast
       qed        
       thus ?thesis using a01 by blast
     qed 
     moreover have "fst (((C, st) # (C', st') # xsa) ! 0)\<noteq>Q" 
       using CptnComp by fastforce     
     ultimately have ?thesis using CptnComp(5)
       using fst_conv length_Cons less_Suc_eq_0_disj nth_Cons_Suc by auto 
    }
    thus ?thesis using a1 by auto    
  next
    case (FaultPropc) thus ?thesis 
      using c_seq redex_not_Seq by blast 
  next
    case (StuckPropc) thus ?thesis 
      using c_seq redex_not_Seq by blast
  next
    case (AbruptPropc) thus ?thesis 
      using c_seq redex_not_Seq by blast
  qed(auto)
qed

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
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p, R, G, q,a] \<Longrightarrow>
       \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [q, R, G, r,a] \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c2 sat [q, R, G, r,a] \<Longrightarrow>        
       Sta a R \<Longrightarrow>  (\<forall>s. (Normal s,Normal s) \<in> G) \<Longrightarrow> Norm R \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> (Seq c1 c2) sat [p, R, G, r,a]"
proof -  
  assume
    a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p, R, G, q,a]" and
    a1:"\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p, R, G, q,a]" and
    a2:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [q, R, G, r,a]" and    
    a3: "\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c2 sat [q, R, G, r,a]" and 
    a4: "Sta a R" and 
    a5: "(\<forall>s. (Normal s, Normal s) \<in> G)" and
    a6: "Norm R"      
  { 
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"
    then have a1:"\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p, R, G, q,a]" 
      using a1 com_cvalidity_def by fastforce  
    then have a3: "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c2 sat [q, R, G, r,a]"
      using a3 com_cvalidity_def all_call by fastforce 
    have "cp \<Gamma> (Seq c1 c2)  s \<inter> assum(p, R) F \<subseteq> comm(G, (r,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cp \<Gamma> (Seq c1 c2) s" and a11:"c \<in> assum(p, R) F"
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have cp:"l!0=((Seq c1 c2),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
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
             then have "False" using a6 no_c2 env_tran_right cp cptn_eq_cptn_mod_set Seq_sound3
               by blast
             thus ?thesis by auto
           next             
             assume asm0:"fst (last l) = LanguageCon.com.Throw \<and> snd (last l) = Normal s'"
             then obtain lc1 s1' ys where cp_lc1:"(\<Gamma>,lc1) \<in> cp \<Gamma> c1 s \<and> l = ((map (lift c2) lc1)@((Throw, Normal s1')#ys))"
               using Seq_sound2[of \<Gamma> l c1 c2 s s'] a6 cp cptn_eq_cptn_mod_set env_tran_right no_c2 by blast
             let ?m_lc1 = "map (lift c2) lc1"
             let ?lm_lc1 = "(length ?m_lc1)"
             let ?last_m_lc1 = "?m_lc1!(?lm_lc1-1)"             
             have lc1_not_empty:"lc1 \<noteq> []"
               using \<Gamma>1 a10 cp_def cp_lc1 by force
             then have map_cp:"(\<Gamma>,?m_lc1) \<in> cp \<Gamma> (Seq c1 c2) s"               
             proof -
               have f1: "lc1 ! 0 = (c1, s) \<and> (\<Gamma>, lc1) \<in> cptn \<and> \<Gamma> = \<Gamma>"
                 using cp_lc1 cp_def by blast
               then have f2: "(\<Gamma>, ?m_lc1) \<in> cptn" using lc1_not_empty
                 by (meson lift_is_cptn)                
               then show ?thesis
                 using f2 f1 lc1_not_empty by (simp add: cp_def lift_def)
             qed
             also have map_assum:"(\<Gamma>,?m_lc1) \<in> assum (p,R) F"
               using sub_assum a10 a11 \<Gamma>1 cp_lc1 lc1_not_empty 
               by (metis SmallStepCon.nth_tl map_is_Nil_conv)
             ultimately have "((\<Gamma>,lc1) \<in> assum(p, R) F)"  
               using \<Gamma>1 assum_map cp_lc1 by blast                          
             then have lc1_comm:"(\<Gamma>,lc1) \<in> comm(G, (q,a)) F"  
               using a1 cp_lc1 by (meson IntI com_validity_def contra_subsetD)
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
               using cp_lc1
               by (simp add:lc1_not_empty nth_append)
             then have lm_lc1:"l!(?lm_lc1) = (Throw, Normal s1')"
               using cp_lc1 by (meson nth_append_length) 
             then have "\<Gamma>\<turnstile>\<^sub>c(l!(?lm_lc1-1)) \<rightarrow> (l!(?lm_lc1))"
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
                   using f2 f1 by (metis (no_types) One_nat_def cp cp_lc1 cptn_tran_ce_i diff_zero)
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
               by (metis One_nat_def asm0 append_is_Nil_conv cp_lc1 diff_Suc_less fst_conv l_map last_conv_nth last_m_lc1 length_greater_0_conv list.simps(3) local.last_length no_c2 snd_conv)                            
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
                    by (metis (no_types) cp_lc1  nth_append)
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
                      by (metis (no_types) Suc_lessI True a21 i_m_l l_map zero_less_diff)
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
                      have "env_tran_right \<Gamma>1 l R"
                        by (metis cp env_tran_right)
                      then show ?thesis
                        by (metis (no_types) a6 cp fst_conv length_map lm_lc1 only_one_component_tran_j snd_conv)
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
               have "?lm_lc1 \<le> length l -1" using cp_lc1 by fastforce
               also have "\<forall>i. ?lm_lc1 \<le>i \<and> i<(length l -1) \<longrightarrow>  \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))"
                 using lm_lc1 cp_lc1 env_tran_right final_always_env_i
               proof -
                 have "env_tran_right \<Gamma>1 (map (lift c2) lc1 @ (LanguageCon.com.Throw, Normal s1') # ys) R"
                   using cp cp_lc1 env_tran_right by presburger
                 then show ?thesis 
                   by (metis (no_types) a6 Suc_eq_plus1 cp cp_lc1 final_always_env_i fst_conv less_diff_conv lm_lc1 snd_conv)
               qed                  
               ultimately have "snd (l ! (length l - 1)) \<in> Normal ` a"
                 using a6 cp_lc1 a_normal a4 env_tran_right stability[of a R l ?lm_lc1 "(length l) -1" _ \<Gamma>] 
                 by fastforce
               thus ?thesis using l_t 
                 by (simp add:  cp_lc1 last_conv_nth)
             qed
             note res = conjI [OF concl concr]
             then show ?thesis using  \<Gamma>1 c_prod unfolding comm_def by auto
           qed                  
         next
           case False
           then obtain lc1 where cp_lc1:"(\<Gamma>,lc1) \<in> cp \<Gamma> c1 s \<and> l = map (lift c2) lc1" 
           using a6 Seq_sound1 False no_c2 env_tran_right cp cptn_eq_cptn_mod_set 
           by blast 
           then have "((\<Gamma>,lc1) \<in> assum(p, R) F)"  
              using \<Gamma>1  a10 a11 assum_map by blast
           then have "(\<Gamma>, lc1)\<in> comm(G, (q,a)) F" using cp_lc1 a1
             by (meson IntI com_validity_def contra_subsetD)
           then have "(\<Gamma>, l)\<in> comm(G, (r,a)) F"
             using comm_map a10 \<Gamma>1 cp_lc1 by fastforce
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
         then obtain lc1 lc2 where cp_lc1:"(\<Gamma>,lc1) \<in> (cp \<Gamma> c1 s) \<and> 
                                 (\<Gamma>,lc2) \<in> (cp \<Gamma> c2 (snd (lc1!(i-1)))) \<and> 
                                 l = (map (lift c2) lc1)@lc2"
           using Seq_sound4 a0 a6 cp env_tran_right by blast  
         have "\<forall>i < length l. snd (l!i) \<notin> Fault ` F"
           using cp l_f last_not_F[of \<Gamma> l F] by blast  
         then have i_not_fault:"snd (l!i) \<notin> Fault ` F" using a0 by blast
         have length_c1_map:"length lc1 = length (map (lift c2) lc1)" 
           by fastforce      
         then have i_map:"i=length lc1" 
           using cp_lc1 li a0 unfolding lift_def
         proof -
            assume a1: "(\<Gamma>, lc1) \<in> cp \<Gamma> c1 s \<and> (\<Gamma>, lc2) \<in> cp \<Gamma> c2 (snd (lc1 ! (i - 1))) \<and> l = map (\<lambda>(P, s). (LanguageCon.com.Seq P c2, s)) lc1 @ lc2"
            have f2: "i < length l \<and> fst (l ! i) = c2 \<and> (\<forall>n. \<not> n < i \<or> fst (l ! n) \<noteq> c2)"
              using a0 by blast
            have f3: "(LanguageCon.com.Seq (fst (lc1 ! i)) c2, snd (lc1 ! i)) = lift c2 (lc1 ! i)"
              by (simp add: case_prod_unfold lift_def)            
            then have "fst (l ! length lc1) = c2"
              using a1 by (simp add: cp_def nth_append)
            thus ?thesis
              using f3 f2 by (metis (no_types) nth_append cp_lc1 fst_conv length_map lift_nth linorder_neqE_nat seq_and_if_not_eq(4))
         qed                  
         have lc2_l:"\<forall>j<length lc2. lc2!j=l!(i+j)"
           using cp_lc1 length_c1_map i_map a0
           by (metis nth_append_length_plus)                                                             
         have lc1_not_empty:"lc1 \<noteq> []"
           using cp cp_lc1 unfolding cp_def by fastforce      
         have lc2_not_empty:"lc2 \<noteq> []"
           using cp_def cp_lc1 cptn.simps by blast             
         have l_is:"s2= snd (last lc1)"
         using cp_lc1 li a0 lc1_not_empty unfolding cp_def
          proof -
            assume a1: "(\<Gamma>, lc1) \<in> {(\<Gamma>1, l). l ! 0 = (c1, s) \<and> (\<Gamma>, l) \<in> cptn \<and> \<Gamma>1 = \<Gamma>} \<and> (\<Gamma>, lc2) \<in> {(\<Gamma>1, l). l ! 0 = (c2, snd (lc1 ! (i - 1))) \<and> (\<Gamma>, l) \<in> cptn \<and> \<Gamma>1 = \<Gamma>} \<and> l = map (lift c2) lc1 @ lc2"
            then have "(map (lift c2) lc1 @ lc2) ! length (map (lift c2) lc1) = l ! i"
              using i_map by force
            have f2: "(c2, s2) = lc2 ! 0"
              using li lc2_l lc2_not_empty by fastforce
            have "op - i = op - (length lc1)"
              using i_map by blast
            then show ?thesis
              using f2 a1 by (simp add: last_conv_nth lc1_not_empty)
          qed 
         let ?m_lc1 = "map (lift c2) lc1"
         (* let ?lm_lc1 = "(length ?m_lc1)"
         let ?last_m_lc1 = "?m_lc1!(?lm_lc1-1)" *)                         
         have last_m_lc1:"l!(i-1) = (Seq (fst (last lc1)) c2,s2)"
         proof -
           have a000:"\<forall>p c. (LanguageCon.com.Seq (fst p) c, snd p) = lift c p"
             using Cons_lift by force
           then show ?thesis
           proof -
             have "length (map (lift c2) lc1) = i"
               using i_map by fastforce
             then show ?thesis
               by (metis (no_types) One_nat_def l_is a000 cp_lc1 diff_less last_conv_nth last_map lc1_not_empty length_c1_map length_greater_0_conv less_Suc0 nth_append)
           qed            
         qed  
         have last_mcl1_not_F:"snd (last ?m_lc1) \<notin> Fault ` F"                 
         proof -
          have "map (lift c2) lc1 \<noteq> []"
            by (metis lc1_not_empty list.map_disc_iff)
          then show ?thesis
            by (metis (full_types) One_nat_def i_not_fault l_is last_conv_nth last_snd lc1_not_empty li snd_conv)
         qed        
         have map_cp:"(\<Gamma>,?m_lc1) \<in> cp \<Gamma> (Seq c1 c2) s"               
         proof -
           have f1: "lc1 ! 0 = (c1, s) \<and> (\<Gamma>, lc1) \<in> cptn \<and> \<Gamma> = \<Gamma>"
             using cp_lc1 cp_def by blast
           then have f2: "(\<Gamma>, ?m_lc1) \<in> cptn" using lc1_not_empty
             by (meson lift_is_cptn)                
           then show ?thesis
             using f2 f1 lc1_not_empty by (simp add: cp_def lift_def)
         qed
         also have map_assum:"(\<Gamma>,?m_lc1) \<in> assum (p,R) F"
           using sub_assum a10 a11 \<Gamma>1 cp_lc1 lc1_not_empty 
           by (metis SmallStepCon.nth_tl map_is_Nil_conv)
         ultimately have "((\<Gamma>,lc1) \<in> assum(p, R) F)"  
           using \<Gamma>1 assum_map using assum_map cp_lc1 by blast                          
         then have lc1_comm:"(\<Gamma>,lc1) \<in> comm(G, (q,a)) F"  
           using a1 cp_lc1 by (meson IntI com_validity_def contra_subsetD)
         then have m_lc1_comm:"(\<Gamma>,?m_lc1) \<in> comm(G, (q,a)) F"
           using map_cp map_assum comm_map cp_lc1 by fastforce         
         then have "\<Gamma>\<turnstile>\<^sub>c(l!(i-1)) \<rightarrow> (l!i)"
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
         then have Normals2:"s2 = Normal s2'" by (simp add: l_is) 
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
                {assume "c2=Throw"
                 then have "\<forall>k. k\<ge>i \<and> (Suc k < length l) \<longrightarrow> 
                            \<not>(\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
                 using li Normals2 
                   by (metis a6 a0  cp env_tran_right only_one_component_tran_j snd_conv)
                 then have ?thesis using a21 a001 k a00 by blast
                }  note left=this
                {assume "c2\<noteq>Throw"
                 then have "fst (last lc1) = Skip"
                   using last_m_lc1 last_lc1
                   by (metis step a0 l_is li prod.collapse stepc_Normal_elim_cases(11) stepc_Normal_elim_cases(5))                 
                 then have s2_normal:"s2 \<in> Normal ` q" 
                   using normal_last lastlc1_normal Normals2
                   by fastforce
                 have length_lc2:"length l=i+length lc2" 
                       using i_map cp_lc1 by fastforce
                 have "(\<Gamma>,lc2) \<in>  assum (q,R) F" 
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
                 also have "(\<Gamma>,lc2) \<in> cp \<Gamma> c2 s2"
                   using cp_lc1 i_map l_is last_conv_nth lc1_not_empty by fastforce
                 ultimately have comm_lc2:"(\<Gamma>,lc2) \<in>  comm (G, (r,a)) F"
                   using a3 unfolding com_validity_def by auto
                 have lc2_last_f:"snd (last lc2)\<notin> Fault ` F" 
                   using lc2_l lc2_not_empty l_f cp_lc1 by fastforce
                 have suck':"Suc k' < length lc2" 
                   using k' a00 length_lc2 by arith
                 moreover then have "\<Gamma>\<turnstile>\<^sub>c(lc2!k')  \<rightarrow> (lc2!(Suc k'))"  
                   using k' lc2_l a21 by fastforce
                 ultimately have "(snd (lc2! k'), snd (lc2 ! Suc k')) \<in> G"
                   using comm_lc2 a6 lc2_last_f comm_dest1[of \<Gamma> lc2 G r a F k'] 
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
             have Throw:"fst (l!(length l - 1)) = Throw"
             using a6 li Normals2  env_tran_right cp c2_throw a0
                     i_throw_all_throw[of \<Gamma> l i s2' "(length l) - 1" _ R] 
                by fastforce                       
             have s2_a:"s2 \<in> Normal ` (a)"
               using normal_last 
               by (simp add: lst_lc1_throw l_is)
             then have "\<forall>ia. i \<le> ia \<and> ia < length l - 1 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c l ! ia \<rightarrow>\<^sub>e l ! Suc ia"
               using c2_throw li Normals2 a0 cp env_tran_right final_always_env_i final_def
             proof -
              have "\<forall>n. \<not> i \<le> n \<or> \<not> n < length l - 1 \<or> \<Gamma>\<turnstile>\<^sub>c l ! n \<rightarrow>\<^sub>e l ! Suc n"
                by (metis (no_types) a6 Normals2 One_nat_def a0 add.right_neutral add_Suc_right c2_throw cp env_tran_right final_always_env_i less_diff_conv li snd_conv)
              then show ?thesis
                by meson
             qed               
             then have "snd (l!(length l - 1)) \<in> Normal ` (a) \<and> fst (l!(length l - 1)) = Throw"
               using a6 a0 s2_a li a4 env_tran_right stability[of a R l i "(length l) -1" _ \<Gamma>] Throw
               by (metis One_nat_def Suc_pred length_greater_0_conv lessI linorder_not_less list.size(3) not_less0 not_less_eq_eq snd_conv)
                              
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
             have "(\<Gamma>,lc2) \<in>  assum (q,R) F" 
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
             also have "(\<Gamma>,lc2) \<in> cp \<Gamma> c2 s2"
               using cp_lc1 i_map l_is last_conv_nth lc1_not_empty by fastforce
             ultimately have comm_lc2:"(\<Gamma>,lc2) \<in>  comm (G, (r,a)) F"
               using a3 unfolding com_validity_def by auto
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
 } thus ?thesis by (simp add: com_validity_def[of \<Gamma>] com_cvalidity_def) 
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
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Catch c1 c2) s) \<and> ((\<Gamma>,l1) \<in> assum(p, R) F)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift_catch c2) l2"  
shows
  "((\<Gamma>,l2) \<in> assum(p, R) F)"
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
    } thus "(\<Gamma>, l2) \<in> assum (p, R) F" 
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
  a0:"(\<Gamma>,x)\<in>cptn_mod" and
  a1:"x!0 = ((Catch P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"\<not> final (last x)" and
  a4:"env_tran_right \<Gamma> x rely \<and> Norm rely"
shows
  "\<exists>xs. (\<Gamma>,xs) \<in> cp \<Gamma> P s \<and> x = map (lift_catch Q) xs"
using a0 a1 a2 a3 a4
proof (induct arbitrary: P s)
  case (CptnModOne \<Gamma> C s1)
  then have "(\<Gamma>, [(P,s)]) \<in> cp \<Gamma> P s \<and> [(C, s1)] = map (lift_catch Q) [(P,s)]"
    unfolding cp_def lift_catch_def  by (simp add: cptn.CptnOne) 
  thus ?case by fastforce
next
  case (CptnModEnv \<Gamma> C s1 t1 xsa)
  then have C:"C=Catch P Q" unfolding lift_catch_def by fastforce
  have "\<exists>xs. (\<Gamma>, xs) \<in> cp \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift_catch Q) xs"
  proof -
     have "((C, t1) # xsa) ! 0 = (Catch P Q, t1)" using C by auto
     moreover have "\<forall>i<length ((C, t1) # xsa). fst (((C, t1) # xsa) ! i) \<noteq> Q"
       using CptnModEnv(5) by fastforce
     moreover have "\<not> SmallStepCon.final (last ((C, t1) # xsa))" using CptnModEnv(6) 
       by fastforce
     ultimately show ?thesis
       using CptnModEnv(3) CptnModEnv(7) env_tran_tail by blast     
  qed 
  then obtain xs where hi:"(\<Gamma>, xs) \<in> cp \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift_catch Q) xs"
    by fastforce
  have s1_s:"s1=s" using  CptnModEnv unfolding cp_def by auto
  obtain xsa' where xs:"xs=((P,t1)#xsa') \<and> (\<Gamma>,((P,t1)#xsa'))\<in>cptn \<and> (C, t1) # xsa = map (lift_catch Q) ((P,t1)#xsa')" 
    using hi  unfolding cp_def by fastforce
  
  have env_tran:"\<Gamma>\<turnstile>\<^sub>c(P,s1) \<rightarrow>\<^sub>e (P,t1)" using CptnModEnv Catch_env_P by (metis fst_conv nth_Cons_0)  
  then have "(\<Gamma>,(P,s1)#(P,t1)#xsa')\<in>cptn" using xs env_tran CptnEnv by fastforce  
  then have "(\<Gamma>,(P,s1)#(P,t1)#xsa') \<in> cp \<Gamma> P s" 
    using cp_def s1_s by fastforce
  moreover have "(C,s1)#(C, t1) # xsa = map (lift_catch Q) ((P,s1)#(P,t1)#xsa')"
    using xs C unfolding lift_catch_def by fastforce
  ultimately show ?case by auto
next
  case (CptnModSkip)
  thus ?case by (metis SmallStepCon.redex_not_Catch fst_conv nth_Cons_0)
next
  case (CptnModThrow)
  thus ?case by (metis SmallStepCon.redex_not_Catch fst_conv nth_Cons_0)
next
  case (CptnModCatch1 \<Gamma> P0 sa xsa zs P1)
  then have a1:"LanguageCon.com.Catch P Q = LanguageCon.com.Catch P0 P1"
    by fastforce  
  have f1: "sa = s"
    using CptnModCatch1.prems(1) by force
  have f2: "P = P0 \<and> Q = P1" using a1 by auto
  have "(\<Gamma>, (P0, sa) # xsa) \<in> cptn"
    by (metis CptnModCatch1.hyps(1) cptn_eq_cptn_mod_set)
  hence "(\<Gamma>, (P0, sa) # xsa) \<in> cp \<Gamma> P s"
    using f2 f1 by (simp add: cp_def)
  thus ?case
    using Cons_lift_catch CptnModCatch1.hyps(3) a1 by blast   
next
 case (CptnModCatch2 \<Gamma> P1 sa xsa  ys zs Q1)
  have "final (last ((Skip, sa)# ys))"
  proof -
    have cptn:"(\<Gamma>, (Skip,snd (last ((P1, sa) # xsa))) # ys) \<in> cptn" 
      using CptnModCatch2(4) by (simp add: cptn_eq_cptn_mod_set)
    moreover have throw_0:"((Skip,snd (last ((P1, sa) # xsa))) # ys)!0 = (Skip, snd (last ((P1, sa) # xsa))) \<and> 0 < length((Skip, snd (last ((P1, sa) # xsa))) # ys)"
      by force         
    moreover have last:"last ((Skip,snd (last ((P1, sa) # xsa))) # ys) = 
                      ((Skip,snd (last ((P1, sa) # xsa))) # ys)!((length ((Skip,snd (last ((P1, sa) # xsa))) # ys)) - 1)"
      using last_conv_nth by auto
    moreover have env_tran:"env_tran_right \<Gamma> ((Skip,snd (last ((P1, sa) # xsa))) # ys) rely" 
      using  CptnModCatch2.hyps(6) CptnModCatch2.prems(4) env_tran_subl env_tran_tail by blast          
    ultimately obtain st' where "fst (last ((Skip,snd (last ((P1, sa) # xsa))) # ys)) = Skip \<and>        
                     snd (last ((Skip,snd (last ((P1, sa) # xsa))) # ys)) = Normal st'" 
    using  CptnModCatch2 zero_skip_all_skip[of \<Gamma> "((Skip,snd (last ((P1, sa) # xsa))) # ys)" "(length ((Skip,snd (last ((P1, sa) # xsa))) # ys))-1"]
    proof -
      have False
        by (metis (no_types) One_nat_def SmallStepCon.final_def \<open>(\<Gamma>, (LanguageCon.com.Skip, snd (last ((P1, sa) # xsa))) # ys) \<in> cptn \<and> fst (((LanguageCon.com.Skip, snd (last ((P1, sa) # xsa))) # ys) ! 0) = LanguageCon.com.Skip \<and> length ((LanguageCon.com.Skip, snd (last ((P1, sa) # xsa))) # ys) - 1 < length ((LanguageCon.com.Skip, snd (last ((P1, sa) # xsa))) # ys) \<Longrightarrow> fst (((LanguageCon.com.Skip, snd (last ((P1, sa) # xsa))) # ys) ! (length ((LanguageCon.com.Skip, snd (last ((P1, sa) # xsa))) # ys) - 1)) = LanguageCon.com.Skip\<close> \<open>\<not> SmallStepCon.final (last ((LanguageCon.com.Catch P1 Q1, sa) # zs))\<close> \<open>zs = map (lift_catch Q1) xsa @ (LanguageCon.com.Skip, snd (last ((P1, sa) # xsa))) # ys\<close> append_is_Nil_conv cptn diff_Suc_Suc diff_zero fst_conv last last.simps last_appendR length_Cons lessI list.simps(3) throw_0)
      then show ?thesis
        by metis
    qed
    thus ?thesis using final_def by (metis fst_conv last.simps)       
  qed
  thus ?case 
    by (metis (no_types, lifting) CptnModCatch2.hyps(3) CptnModCatch2.hyps(6) CptnModCatch2.prems(3) SmallStepCon.final_def append_is_Nil_conv last.simps last_appendR list.simps(3) prod.collapse)     
next
  case (CptnModCatch3 \<Gamma> P0 sa xsa sa' P1 ys zs)
  then have "P0 = P \<and> P1 = Q" by auto
  then obtain i where zs:"fst (zs!i) = Q \<and> (i< (length zs))" 
    using CptnModCatch3
    by (metis (no_types, lifting) add_diff_cancel_left' fst_conv length_Cons length_append nth_append_length zero_less_Suc zero_less_diff)    
  then have "Suc i< length ((Catch P0 P1,Normal sa)#zs)" by fastforce
  then have "fst (((Catch P0 P1, Normal sa) # zs)!Suc i) = Q" using zs by fastforce    
  thus ?case using CptnModCatch3(9) zs by auto
qed (auto)

lemma Catch_sound2: 
assumes
  a0:"(\<Gamma>,x)\<in>cptn_mod" and
  a1:"x!0 = ((Catch P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"fst (last x) = Skip" and
  a4:"env_tran_right \<Gamma> x rely"
shows
  "\<exists>xs ys. (\<Gamma>,xs) \<in> cp \<Gamma> P s \<and> x = ((map (lift_catch Q) xs)@((Skip,snd(last xs))#ys))"
using a0 a1 a2 a3 a4
proof (induct arbitrary: P s)
  case (CptnModOne \<Gamma> C s1)
  then have "(\<Gamma>, [(P,s)]) \<in> cp \<Gamma> P s \<and> [(C, s1)] = map (lift Q) [(P,s)]@[(Throw, Normal s')]"
    unfolding cp_def lift_def  by (simp add: cptn.CptnOne) 
  thus ?case by fastforce
next
  case (CptnModEnv \<Gamma> C s1 t1 xsa)
  then have C:"C=Catch P Q" unfolding lift_catch_def by fastforce
  have "\<exists>xs ys. (\<Gamma>, xs) \<in> cp \<Gamma> P t1 \<and> (C, t1) # xsa = 
                map (lift_catch Q) xs@((Skip, snd(last xs))#ys)"
  proof -
     have "((C, t1) # xsa) ! 0 = (LanguageCon.com.Catch P Q, t1)" using C by auto
     moreover have "\<forall>i<length ((C, t1) # xsa). fst (((C, t1) # xsa) ! i) \<noteq> Q"
       using CptnModEnv(5) by fastforce
     moreover have "fst (last ((C, t1) # xsa)) = Skip" using CptnModEnv(6) 
       by fastforce
     ultimately show ?thesis
       using CptnModEnv(3) CptnModEnv(7) env_tran_tail by blast    
  qed 
  then obtain xs ys where hi:"(\<Gamma>, xs) \<in> cp \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift_catch Q) xs@((Skip,snd(last ((P, t1)#xs)))#ys)"
    by fastforce
  have s1_s:"s1=s" using  CptnModEnv unfolding cp_def by auto
  have "\<exists>xsa' ys. xs=((P,t1)#xsa') \<and> (\<Gamma>,((P,t1)#xsa'))\<in>cptn \<and> (C, t1) # xsa = map (lift_catch Q) ((P,t1)#xsa')@((Skip, snd(last xs))#ys)" 
    using hi  unfolding cp_def
  proof -
      have "(\<Gamma>,xs)\<in>cptn \<and> xs!0 = (P,t1)" using hi unfolding cp_def by fastforce
      moreover then have "xs\<noteq>[]" using cptn.simps by fastforce  
      ultimately obtain xsa' where "xs=((P,t1)#xsa')" using SmallStepCon.nth_tl by fastforce 
      thus ?thesis
        using hi using \<open>(\<Gamma>, xs) \<in> cptn \<and> xs ! 0 = (P, t1)\<close> by auto 
  qed
  then obtain xsa' ys where xs:"xs=((P,t1)#xsa') \<and> (\<Gamma>,((P,t1)#xsa'))\<in>cptn \<and> (C, t1) # xsa = 
                                    map (lift_catch Q) ((P,t1)#xsa')@((Skip,snd(last ((P,s1)#(P,t1)#xsa')))#ys)"
    by fastforce
  have env_tran:"\<Gamma>\<turnstile>\<^sub>c(P,s1) \<rightarrow>\<^sub>e (P,t1)" using CptnModEnv Catch_env_P by (metis fst_conv nth_Cons_0)  
  then have "(\<Gamma>,(P,s1)#(P,t1)#xsa')\<in>cptn" using xs env_tran CptnEnv by fastforce  
  then have "(\<Gamma>,(P,s1)#(P,t1)#xsa') \<in> cp \<Gamma> P s" 
    using cp_def s1_s by fastforce
  moreover have "(C,s1)#(C, t1) # xsa = map (lift_catch Q) ((P,s1)#(P,t1)#xsa')@((Skip,snd(last ((P,s1)#(P,t1)#xsa')))#ys)"
    using xs C unfolding lift_catch_def
    by auto
  ultimately show ?case by fastforce 
next
  case (CptnModSkip)
  thus ?case by (metis SmallStepCon.redex_not_Catch fst_conv nth_Cons_0)
next
  case (CptnModThrow)
  thus ?case by (metis SmallStepCon.redex_not_Catch fst_conv nth_Cons_0)
next
  case (CptnModCatch1 \<Gamma> P0 sa xsa zs P1)  
  thus ?case
  proof -
    have "\<forall>c x. (LanguageCon.com.Catch c P1, x) # zs = map (lift_catch P1) ((c, x) # xsa)"
      using Cons_lift_catch CptnModCatch1.hyps(3) by blast
    then have "(P0, sa) # xsa = []"
      by (metis (no_types) CptnModCatch1.prems(3) LanguageCon.com.distinct(19) One_nat_def last_conv_nth last_lift_catch map_is_Nil_conv)
    then show ?thesis
      by force
  qed 
next
  case (CptnModCatch2 \<Gamma> P1 sa xsa  ys zs Q1) 
  then have "P1 = P \<and> Q1 = Q \<and> sa = s" by auto  
  moreover then have "(\<Gamma>, (P1,sa) # xsa)\<in> cp \<Gamma> P s" 
    using CptnModCatch2(1)
    by (simp add: cp_def cptn_eq_cptn_mod_set)  
  moreover obtain s' where "last zs=(Skip, s')" 
  proof -
    assume a1: "\<And>s'. last zs = (LanguageCon.com.Skip, s') \<Longrightarrow> thesis"
    have "\<exists>x. last zs = (LanguageCon.com.Skip, x)"
      by (metis (no_types) CptnModCatch2.hyps(6) CptnModCatch2.prems(3) append_is_Nil_conv last_ConsR list.simps(3) prod.exhaust_sel)
    then show ?thesis
      using a1 by metis
  qed        
  ultimately show ?case 
    using Cons_lift_catch_append CptnModCatch2.hyps(6)  by fastforce  
next 
  case (CptnModCatch3 \<Gamma> P0 sa xsa sa' P1 ys zs)   
  then have "P0 = P \<and> P1 = Q \<and> s=Normal sa" by auto
  then obtain i where zs:"fst (zs!i) = Q \<and> (i< (length zs))" 
    using CptnModCatch3    
    by (metis (no_types, lifting) add_diff_cancel_left' fst_conv length_Cons length_append nth_append_length zero_less_Suc zero_less_diff)    
  then have si:"Suc i< length ((Catch P0 P1,Normal sa)#zs)" by fastforce
  then have "fst (((Seq P0 P1, Normal sa) # zs)!Suc i) = Q" using zs by fastforce    
  thus ?case using CptnModCatch3(9) zs
     by (metis si nth_Cons_Suc)
qed (auto)

lemma Catch_sound3: 
assumes
  a0:"(\<Gamma>,x)\<in>cptn" and
  a1:"x!0 = ((Catch P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"fst(last x) = Throw" and
  a4:"env_tran_right \<Gamma> x rely \<and> Norm rely"
shows
  "False"
using a0 a1 a2 a3 a4
proof (induct arbitrary: P s)
  case (CptnOne \<Gamma> C s1) thus ?case by auto
next
  case (CptnEnv \<Gamma> C st t xsa) 
    thus ?case
    proof -
      have f1: "env_tran_right \<Gamma> ((C, t) # xsa) rely \<and> Norm rely"
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
      have f1: "env_tran_right \<Gamma> ((C', st') # xsa) rely \<and> Norm rely"
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
        by (metis (no_types) CptnComp.hyps(2) CptnComp.prems(3) LanguageCon.com.distinct(17) last_ConsR last_length length_Cons lessI list.simps(3) zero_skip_all_skip)
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


lemma Catch_sound4: 
assumes
  a0:"(\<Gamma>,x)\<in>cptn" and
  a1:"x!0 = ((Catch P Q),s)" and
  a2:"i<length x \<and> x!i=(Q,sj)" and
  a3:"\<forall>j<i. fst(x!j)\<noteq>Q" and 
  a4:"env_tran_right \<Gamma> x rely \<and> Norm rely"
shows
  "\<exists>xs ys. (\<Gamma>,xs) \<in> (cp \<Gamma> P s) \<and> (\<Gamma>,ys) \<in> (cp \<Gamma> Q (snd (xs!(i-1)))) \<and> x = (map (lift_catch Q) xs)@ys"
using a0 a1 a2 a3 a4
proof (induct arbitrary: i sj P s) 
  case (CptnOne \<Gamma>1 P1 s1) 
    thus ?case by auto    
next
  case (CptnEnv \<Gamma> C st t xsa)    
  have a1:"Catch P Q \<noteq> Q" by simp    
  then have C_catch:"C=(Catch P Q)" using CptnEnv by fastforce
  then have "fst(((C, st) # (C, t) # xsa)!0) \<noteq>Q" using CptnEnv a1 by auto
  moreover have  "fst(((C, st) # (C, t) # xsa)!1) \<noteq>Q" using CptnEnv a1 by auto
  moreover have "fst(((C, st) # (C, t) # xsa)!i) =Q" using CptnEnv by auto
  ultimately have i_suc: "i> (Suc 0)" using CptnEnv 
    by (metis Suc_eq_plus1 Suc_lessI add.left_neutral neq0_conv) 
  then obtain i' where i':"i=Suc i'" by (meson lessE) 
  then have i_minus:"i'=i-1" by auto  
  have "((C, t) # xsa) ! 0 = ((Catch P Q), t)"
    using CptnEnv by auto 
  moreover have "i'< length ((C,t)#xsa) \<and> ((C,t)#xsa)!i' = (Q,sj)"
    using i' CptnEnv(5) by force
  moreover have "\<forall>j<i'. fst (((C, t) # xsa) ! j) \<noteq> Q"
    using i' CptnEnv(6) by force
  ultimately have hyp:"\<exists>xs ys.
     (\<Gamma>, xs) \<in> cp \<Gamma> P t \<and>
     (\<Gamma>, ys) \<in> cp \<Gamma> Q (snd (xs ! (i'-1))) \<and> (C, t) # xsa = map (lift_catch Q) xs @ ys"
    using CptnEnv(3) env_tran_tail CptnEnv.prems(4)  by blast 
  then obtain xs ys where xs_cp:"(\<Gamma>, xs) \<in> cp \<Gamma> P t \<and>
     (\<Gamma>, ys) \<in> cp \<Gamma> Q (snd (xs ! (i'-1))) \<and> (C, t) # xsa = map (lift_catch Q) xs @ ys"
    by fast
  have "(\<Gamma>, (P, s)#xs) \<in> cp \<Gamma> P s"
  proof -
    have "xs!0 = (P,t)" 
      using xs_cp unfolding cp_def by blast
    moreover have "xs\<noteq>[]"
      using cp_def cptn.simps xs_cp by blast 
    ultimately obtain xs' where xs':"(\<Gamma>, (P,t)#xs') \<in> cptn \<and> xs=(P,t)#xs'" 
      using SmallStepCon.nth_tl xs_cp unfolding cp_def by force
    thus ?thesis using cp_def  cptn.CptnEnv
    proof -
      have "(Catch P Q, s) = (C, st)"
        using CptnEnv.prems(1) by auto
      then have "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow>\<^sub>e (P, t)"
        using Catch_env_P CptnEnv(1) by blast
      then show ?thesis
        by (simp add:xs' cp_def cptn.CptnEnv)
    qed
  qed
  thus  ?case 
    using i_suc Cons_lift_catch_append CptnEnv.prems(1) i' i_minus xs_cp
    by fastforce   
next
  case (CptnComp \<Gamma> C st C' st' xsa i)
  then have c_catch:"C = (Catch P Q) \<and> st = s" by fastforce  
  from CptnComp show ?case proof(cases)
    case (Catchc P1 P1' P2)      
    then have C_seq:"C=(Catch P Q)" using CptnEnv CptnComp by fastforce    
    then have "fst(((C, st) # (C', st') # xsa)!0) \<noteq>Q" 
      using CptnComp by auto
    moreover have  "fst(((C, st) # (C', st') # xsa)!1) \<noteq>Q" 
      using  CptnComp Catchc by auto
    moreover have "fst(((C, st) # (C', st') # xsa)!i) =Q" 
      using CptnComp by auto
    ultimately have  i_gt0:"i> (Suc 0)" 
      by (metis Suc_eq_plus1 Suc_lessI add.left_neutral neq0_conv) 
    then obtain i' where i':"i=Suc i'" by (meson lessE) 
    then have i_minus:"i'=i-1" by auto       
    have "((C', st') # xsa) ! 0 = ((Catch P1' Q), st')"
      using CptnComp Catchc by auto 
    moreover have "i'< length ((C',st')#xsa) \<and> ((C',st')#xsa)!i' = (Q,sj)"
      using i' CptnComp(5) by force
    moreover have "\<forall>j<i'. fst (((C', st') # xsa) ! j) \<noteq> Q"
    using i' CptnComp(6) by force   
    ultimately have "\<exists>xs ys.
       (\<Gamma>, xs) \<in> cp \<Gamma> P1' st' \<and>
       (\<Gamma>, ys) \<in> cp \<Gamma> Q (snd (xs ! (i'-1))) \<and> (C', st') # xsa = map (lift_catch Q) xs @ ys"
    using CptnComp Catchc env_tran_tail CptnComp.prems(4) by blast
    then obtain xs ys where xs_cp:
      "(\<Gamma>, xs) \<in> cp \<Gamma> P1' st' \<and>
       (\<Gamma>, ys) \<in> cp \<Gamma> Q (snd (xs ! (i'-1))) \<and> (C', st') # xsa = map (lift_catch Q) xs @ ys"
      by fastforce
     have "(\<Gamma>, (P,s)#xs) \<in> cp \<Gamma> P s"        
     proof -
        have "xs!0 = (P1',st')" 
          using xs_cp unfolding cp_def by blast
        moreover have "xs\<noteq>[]"
          using cp_def cptn.simps xs_cp by blast 
        ultimately obtain xs' where xs':"(\<Gamma>, (P1',st')#xs') \<in> cptn \<and> xs=(P1',st')#xs'" 
          using SmallStepCon.nth_tl xs_cp unfolding cp_def by force
        thus ?thesis using cp_def  cptn.CptnEnv Catchc c_catch
              xs' cp_def cptn.CptnComp          
             by (simp add: cp_def cptn.CptnComp xs') 
     qed     
     thus ?thesis using Cons_lift_catch c_catch i' xs_cp i_gt0 by fastforce
  next
    case (CatchSkipc) 
    with CptnComp have PC:"P=Skip \<and> C'=Skip \<and> st=st' \<and> s=st" by fastforce   
    then have all_skip:"\<forall>j\<ge>0. j< (length ((C',st')#xsa)) \<longrightarrow> fst(((C',st')#xsa)!j) = Skip"       
      by (metis (no_types) CptnComp.hyps(2) PC fst_conv i_skip_all_skip nth_Cons_0)
    then have Q_skip:"Q=Skip" 
    proof - 
      have "Catch Skip Q\<noteq>Q" by auto
      then show "Q=Skip"         
        using all_skip CptnComp(4,5,6)  PC less_Suc_eq_0_disj  
        by auto
    qed
    then have "(\<Gamma>, [(Skip,st)]) \<in> cp \<Gamma> P s" unfolding cp_def using cptn.simps PC
      by fastforce    
    moreover have "(\<Gamma>, (Q,st')#xsa) \<in> cp \<Gamma> Q st'" 
       unfolding cp_def
       using CptnComp PC Q_skip by fastforce
    moreover have "i=1"
    proof -
      have f1: "fst (((C, st) # (C', st') # xsa) ! 0) \<noteq> Q"
        using CptnComp.prems(1) by force        
      have "fst (((C, st) # (C', st') # xsa) ! Suc 0) = LanguageCon.com.Skip"
        using PC by force
      then have f3: "\<not> Suc 0 < i"
        using CptnComp.prems(3) Q_skip by blast
      have "((C, st) # (C', st') # xsa) ! i \<noteq> (C, st)"
        using f1 CptnComp.prems(2) by force
      then have "0 \<noteq> i"
         by force
      then show ?thesis
        using f3 by auto
    qed      
    moreover have "[(Catch Skip Q, st)]  = map (lift_catch Q) [(Skip,st)]" 
      unfolding lift_catch_def by auto
    ultimately show ?thesis using PC CatchSkipc
      using CptnComp.prems(2) PC  c_catch by force 
  next
    case (CatchThrowc s')
    with CptnComp have PC:"P=Throw \<and> C'=Q \<and>  st=st' \<and> st=s" by fastforce        
    then have "(\<Gamma>, [(Throw, Normal s')]) \<in> cp \<Gamma> P s"
      using PC cptn.simps unfolding cp_def 
      using cptn.CptnOne local.CatchThrowc(3) by force
    moreover have "(\<Gamma>, (C', st') # xsa)\<in>cp \<Gamma> Q st' "
       using PC CptnComp unfolding cp_def  by fastforce
     moreover have "i=1" using CptnComp (4-6) PC 
     proof -
       have "fst (((C, st) # (C', st') # xsa) ! Suc 0) = Q"
         using PC by force
       then have "\<not> Suc 0 < i"
         using local.CptnComp(6) by blast 
       have "(LanguageCon.com.Throw, sj) \<noteq> (LanguageCon.com.Seq P Q, s)"
         by blast
       then have "i \<noteq> 0"
         using c_catch local.CptnComp(5) by force
       then have "Suc 0 = i"
         using \<open>\<not> Suc 0 < i\<close> by linarith
       then show ?thesis by auto    
     qed   
     moreover have "[(Catch Throw Q, st)]  = map (lift_catch Q) [(Throw,st)]" 
      unfolding lift_catch_def by auto
     ultimately show ?thesis  using PC CatchThrowc by fastforce     
  next
    case (FaultPropc) thus ?thesis 
      using c_catch redex_not_Catch by blast 
  next
    case (StuckPropc) thus ?thesis 
      using c_catch redex_not_Catch by blast
  next
    case (AbruptPropc) thus ?thesis 
      using c_catch redex_not_Catch by blast
  qed(auto)
qed

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
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p,  R, G, q,r] \<Longrightarrow>
       \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [r,  R, G, q,a] \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c2 sat [r,  R, G, q,a] \<Longrightarrow>        
       Sta q R \<Longrightarrow>  (\<forall>s. (Normal s,Normal s) \<in> G) \<Longrightarrow> Norm R \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> (Catch c1 c2) sat [p, R, G, q,a]"
proof -  
  assume
    a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p, R, G, q,r]" and
    a1:"\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p, R, G, q,r]" and
    a2:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [r, R, G, q,a]" and    
    a3: "\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c2 sat [r, R, G, q,a]" and     
    a4: "Sta q R" and
    a5: "(\<forall>s. (Normal s, Normal s) \<in> G)" and 
    a6: "Norm R"  
  { 
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"
    then have a1:"\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p, R, G, q,r]" 
      using a1 com_cvalidity_def by fastforce  
    then have a3: "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c2 sat [r, R, G, q,a]"
      using a3 com_cvalidity_def all_call by fastforce 
    have "cp \<Gamma> (Catch c1 c2)  s \<inter> assum(p, R) F \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cp \<Gamma> (Catch c1 c2) s" and a11:"c \<in> assum(p, R) F"
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have cp:"l!0=((Catch c1 c2),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
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
             then have "False" using a6 no_c2 env_tran_right cp cptn_eq_cptn_mod_set Catch_sound3
               by blast
             thus ?thesis by auto
           next             
             assume asm0:"fst (last l) = Skip"
             then obtain lc1 ys where cp_lc1:"(\<Gamma>,lc1) \<in> cp \<Gamma> c1 s \<and> l = ((map (lift_catch c2) lc1)@((Skip,snd(last lc1))#ys))"
               using Catch_sound2 cp cptn_eq_cptn_mod_set env_tran_right no_c2 by blast
             let ?m_lc1 = "map (lift_catch c2) lc1"
             let ?lm_lc1 = "(length ?m_lc1)"
             let ?last_m_lc1 = "?m_lc1!(?lm_lc1-1)"              
             have lc1_not_empty:"lc1 \<noteq> []"
               using \<Gamma>1 a10 cp_def cp_lc1 by force             
             then have map_cp:"(\<Gamma>,?m_lc1) \<in> cp \<Gamma> (Catch c1 c2) s"               
             proof -
               have f1: "lc1 ! 0 = (c1, s) \<and> (\<Gamma>, lc1) \<in> cptn \<and> \<Gamma> = \<Gamma>"
                 using cp_lc1 cp_def by blast
               then have f2: "(\<Gamma>, ?m_lc1) \<in> cptn" using lc1_not_empty
                 by (meson lift_catch_is_cptn)                
               then show ?thesis
                 using f2 f1 lc1_not_empty by (simp add: cp_def lift_catch_def)
             qed
             also have map_assum:"(\<Gamma>,?m_lc1) \<in> assum (p,R) F"
               using sub_assum a10 a11 \<Gamma>1 cp_lc1 lc1_not_empty 
               by (metis SmallStepCon.nth_tl map_is_Nil_conv)
             ultimately have "((\<Gamma>,lc1) \<in> assum(p, R) F)"  
               using \<Gamma>1 assum_map_catch cp_lc1 by blast                          
             then have lc1_comm:"(\<Gamma>,lc1) \<in> comm(G, (q,r)) F"  
               using a1 cp_lc1 by (meson IntI com_validity_def contra_subsetD)
             then have m_lc1_comm:"(\<Gamma>,?m_lc1) \<in> comm(G, (q,r)) F"
               using map_cp map_assum comm_map_catch cp_lc1 by fastforce
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
                 have f1: "\<forall>n na. \<not> n < na \<or> Suc (na - Suc n) = na - n"
                   by (meson Suc_diff_Suc)
                 have "map (lift_catch c2) lc1 \<noteq> []"
                   by (metis lc1_not_empty map_is_Nil_conv)
                 then have f2: "0 < length (map (lift_catch c2) lc1)"
                   by (meson length_greater_0_conv)
                 then have "length (map (lift_catch c2) lc1) - 1 + 1 < length (map (lift_catch c2) lc1 @ (Skip,snd (last  lc1)) # ys)"
                   by simp
                 then show ?thesis
                   using f2 f1 by (metis (no_types) One_nat_def cp cp_lc1 cptn_tran_ce_i diff_zero)
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
                 using cp cp_lc1  l_f  last_not_F[of \<Gamma> l F]
                 by fastforce
               ultimately show ?thesis using l_map last_length by fastforce
             qed
             then have q_normal:"snd (l!?lm_lc1) \<in> Normal ` q" 
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
                      have "env_tran_right \<Gamma>1 l R \<and> Norm R"
                        by (metis cp env_tran_right a6)
                      then show ?thesis
                        by (metis (no_types) cp fst_conv length_map lm_lc1 only_one_component_tran_j)
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
               proof -
               { fix nn :: nat
                 have "\<And>n. (n::nat) + 0 = n" by simp
                 then have "\<not> nn < length l - 1 \<or> \<not> length (map (lift_catch c2) lc1) \<le> nn \<or> \<Gamma>\<turnstile>\<^sub>c l ! nn \<rightarrow>\<^sub>e l ! Suc nn"
                   by (metis (no_types) a6 One_nat_def add_Suc_right cp env_tran_right final_always_env_i fst_conv less_diff_conv lm_lc1) 
               } then show ?thesis by blast
               qed                                  
               ultimately have "snd (l ! (length l - 1)) \<in> Normal ` q"
                 using cp_lc1 q_normal a4 a6 env_tran_right stability[of q R l ?lm_lc1 "(length l) -1" _ \<Gamma>] 
                 by fastforce               
               thus ?thesis using l_t 
                 by (simp add:  cp_lc1 last_conv_nth)
             qed
             note res = conjI [OF concl concr]
             then show ?thesis using  \<Gamma>1 c_prod unfolding comm_def by auto
           qed                  
         next
           case False
           then obtain lc1 where cp_lc1:"(\<Gamma>,lc1) \<in> cp \<Gamma> c1 s \<and> l = map (lift_catch c2) lc1" 
           using a6 Catch_sound1 False no_c2 env_tran_right cp cptn_eq_cptn_mod_set 
           by blast 
           then have "((\<Gamma>,lc1) \<in> assum(p, R) F)"  
              using \<Gamma>1  a10 a11 assum_map_catch by blast
           then have "(\<Gamma>, lc1)\<in> comm(G, (q,r)) F" using cp_lc1 a1
             by (meson IntI com_validity_def contra_subsetD)
           then have "(\<Gamma>, l)\<in> comm(G, (q,r)) F"
             using comm_map_catch a10 \<Gamma>1 cp_lc1 by fastforce
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
         then obtain lc1 lc2 where cp_lc1:"(\<Gamma>,lc1) \<in> (cp \<Gamma> c1 s) \<and> 
                                 (\<Gamma>,lc2) \<in> (cp \<Gamma> c2 (snd (lc1!(i-1)))) \<and> 
                                 l = (map (lift_catch c2) lc1)@lc2"
           using Catch_sound4 a0 a6 cp env_tran_right by blast           
         have i_not_fault:"snd (l!i) \<notin> Fault ` F" using a0  cp l_f last_not_F[of \<Gamma> l F] by blast
         have length_c1_map:"length lc1 = length (map (lift_catch c2) lc1)" 
           by fastforce      
         then have i_map:"i=length lc1" 
           using cp_lc1 li a0 unfolding lift_catch_def
         proof -
            assume a1: "(\<Gamma>, lc1) \<in> cp \<Gamma> c1 s \<and> (\<Gamma>, lc2) \<in> cp \<Gamma> c2 (snd (lc1 ! (i - 1))) \<and> l = map (\<lambda>(P, s). (Catch P c2, s)) lc1 @ lc2"
            have f2: "i < length l \<and> fst (l ! i) = c2 \<and> (\<forall>n. \<not> n < i \<or> fst (l ! n) \<noteq> c2)"
              using a0 by blast
            have f3: "(Catch (fst (lc1 ! i)) c2, snd (lc1 ! i)) = lift_catch c2 (lc1 ! i)"
              by (simp add: case_prod_unfold lift_catch_def)            
            then have "fst (l ! length lc1) = c2"
              using a1 by (simp add: cp_def nth_append)
            thus ?thesis
              using f3 f2
              by (metis (no_types, lifting) Pair_inject a0 cp_lc1 f3 length_c1_map li linorder_neqE_nat nth_append nth_map seq_and_if_not_eq(12))
         qed                  
         have lc2_l:"\<forall>j<length lc2. lc2!j=l!(i+j)"
           using cp_lc1 length_c1_map i_map a0
           by (metis nth_append_length_plus)                                                             
         have lc1_not_empty:"lc1 \<noteq> []"
           using cp cp_lc1 unfolding cp_def by fastforce      
         have lc2_not_empty:"lc2 \<noteq> []"
           using cp_def cp_lc1 cptn.simps by blast             
         have l_is:"s2= snd (last lc1)"
         using cp_lc1 li a0 lc1_not_empty unfolding cp_def
          proof -
            assume a1: "(\<Gamma>, lc1) \<in> {(\<Gamma>1, l). l ! 0 = (c1, s) \<and> (\<Gamma>, l) \<in> cptn \<and> \<Gamma>1 = \<Gamma>} \<and> (\<Gamma>, lc2) \<in> {(\<Gamma>1, l). l ! 0 = (c2, snd (lc1 ! (i - 1))) \<and> (\<Gamma>, l) \<in> cptn \<and> \<Gamma>1 = \<Gamma>} \<and> l = map (lift_catch c2) lc1 @ lc2"
            then have "(map (lift_catch c2) lc1 @ lc2) ! length (map (lift_catch c2) lc1) = l ! i"
              using i_map by force
            have f2: "(c2, s2) = lc2 ! 0"
              using li lc2_l lc2_not_empty by fastforce
            have "op - i = op - (length lc1)"
              using i_map by blast
            then show ?thesis
              using f2 a1 by (simp add: last_conv_nth lc1_not_empty)
          qed 
         let ?m_lc1 = "map (lift_catch c2) lc1"
         (* let ?lm_lc1 = "(length ?m_lc1)"
         let ?last_m_lc1 = "?m_lc1!(?lm_lc1-1)" *)                         
         have last_m_lc1:"l!(i-1) = (Catch (fst (last lc1)) c2,s2)"
         proof -
           have a000:"\<forall>p c. (Catch (fst p) c, snd p) = lift_catch c p"
             using Cons_lift_catch by fastforce
           then show ?thesis
           proof -
             have "length (map (lift_catch c2) lc1) = i"
               using i_map by fastforce
             then show ?thesis
               by (metis (no_types) One_nat_def l_is a000 cp_lc1 diff_less last_conv_nth last_map lc1_not_empty length_c1_map length_greater_0_conv less_Suc0 nth_append)
           qed            
         qed  
         have last_mcl1_not_F:"snd (last ?m_lc1) \<notin> Fault ` F"                 
         proof -
          have "map (lift_catch c2) lc1 \<noteq> []"
            by (metis lc1_not_empty list.map_disc_iff)
          then show ?thesis
            by (metis One_nat_def i_not_fault l_is last_conv_nth last_snd_catch lc1_not_empty li snd_conv) 
            (* by (metis One_nat_def i_not_fault l_is last_conv_nth last_snd lc1_not_empty li snd_conv) *)
         qed        
         have map_cp:"(\<Gamma>,?m_lc1) \<in> cp \<Gamma> (Catch c1 c2) s"               
         proof -
           have f1: "lc1 ! 0 = (c1, s) \<and> (\<Gamma>, lc1) \<in> cptn \<and> \<Gamma> = \<Gamma>"
             using cp_lc1 cp_def by blast
           then have f2: "(\<Gamma>, ?m_lc1) \<in> cptn" using lc1_not_empty
             by (meson lift_catch_is_cptn)                
           then show ?thesis
             using f2 f1 lc1_not_empty by (simp add: cp_def lift_catch_def)
         qed
         also have map_assum:"(\<Gamma>,?m_lc1) \<in> assum (p,R) F"
           using sub_assum a10 a11 \<Gamma>1 cp_lc1 lc1_not_empty 
           by (metis SmallStepCon.nth_tl map_is_Nil_conv)
         ultimately have "((\<Gamma>,lc1) \<in> assum(p, R) F)"  
           using \<Gamma>1 assum_map_catch using assum_map cp_lc1 by blast                          
         then have lc1_comm:"(\<Gamma>,lc1) \<in> comm(G, (q,r)) F"  
           using a1 cp_lc1 by (meson IntI com_validity_def contra_subsetD)
         then have m_lc1_comm:"(\<Gamma>,?m_lc1) \<in> comm(G, (q,r)) F"
           using map_cp map_assum comm_map_catch cp_lc1 by fastforce         
         then have "\<Gamma>\<turnstile>\<^sub>c(l!(i-1)) \<rightarrow> (l!i)"
         proof -
           have "\<Gamma>\<turnstile>\<^sub>c(l!(i-1)) \<rightarrow>\<^sub>c\<^sub>e (l!(i))"
           proof -
             have f1: "\<forall>n na. \<not> n < na \<or> Suc (na - Suc n) = na - n"
               by (meson Suc_diff_Suc)
             have "map (lift_catch c2) lc1 \<noteq> []"
               by (metis lc1_not_empty map_is_Nil_conv)
             then have f2: "0 < length (map (lift_catch c2) lc1)"
               by (meson length_greater_0_conv)             
             then have "length (map (lift_catch c2) lc1) - 1 + 1 < length (map (lift_catch c2) lc1 @ lc2)"
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
                {assume "c2=Skip"
                 then have "\<forall>k. k\<ge>i \<and> (Suc k < length l) \<longrightarrow> 
                            \<not>(\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
                 using li Normals2 
                   by (metis a0  a6 cp env_tran_right only_one_component_tran_j)
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
                 have "(\<Gamma>,lc2) \<in>  assum (r,R) F" 
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
                 also have "(\<Gamma>,lc2) \<in> cp \<Gamma> c2 s2"
                   using cp_lc1 i_map l_is last_conv_nth lc1_not_empty by fastforce
                 ultimately have comm_lc2:"(\<Gamma>,lc2) \<in>  comm (G, (q,a)) F"
                   using a3 unfolding com_validity_def by auto
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
             using li Normals2  env_tran_right cp c2_skip a0
                     i_skip_all_skip[of \<Gamma> l i "(length l) - 1" _] 
                by fastforce                       
             have s2_a:"s2 \<in> Normal ` q"
               using normal_last 
               by (simp add: lst_lc1_skip l_is)
             then have "\<forall>ia. i \<le> ia \<and> ia < length l - 1 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c l ! ia \<rightarrow>\<^sub>e l ! Suc ia"
               using c2_skip li Normals2 a0 cp env_tran_right final_always_env_i final_def
             proof -
              have "\<forall>n. \<not> i \<le> n \<or> \<not> n < length l - 1 \<or> \<Gamma>\<turnstile>\<^sub>c l ! n \<rightarrow>\<^sub>e l ! Suc n"
                using a6 a0 c2_skip cp env_tran_right final_always_env_i by fastforce              
              then show ?thesis
                by meson
             qed               
             then have "snd (l!(length l - 1)) \<in> Normal ` q \<and> fst (l!(length l - 1)) = Skip"               
               using a6 a0 s2_a li a4 env_tran_right stability[of q R l i "(length l) -1" _ \<Gamma>] Skip                
               by (metis One_nat_def Suc_pred length_greater_0_conv lessI linorder_not_less list.size(3) not_less0 not_less_eq_eq snd_conv)
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
             have "(\<Gamma>,lc2) \<in>  assum (r,R) F" 
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
             also have "(\<Gamma>,lc2) \<in> cp \<Gamma> c2 s2"
               using cp_lc1 i_map l_is last_conv_nth lc1_not_empty by fastforce
             ultimately have comm_lc2:"(\<Gamma>,lc2) \<in>  comm (G, (q,a)) F"
               using a3 unfolding com_validity_def by auto
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
 } thus ?thesis by (simp add: com_validity_def[of \<Gamma>] com_cvalidity_def) 
qed
lemma "\<forall>s t. (q imp I)(s,t) \<longrightarrow> (q imp (I \<and>*sep_true))(s,t)"
by (simp add: sep_conj_sep_true)


lemma DynCom_sound: 
      "(\<forall>s \<in> p. ((\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (c1 s) sat [p, R, G, q,a]) \<and> 
                 (\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> (c1 s) sat [p,R, G, q,a]))) \<Longrightarrow>
        (\<forall>s. (Normal s, Normal s) \<in> G) \<Longrightarrow>
       (Sta p R) \<and> (Sta q R) \<and> (Sta a R) \<and> Norm R \<Longrightarrow>        
        \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> (DynCom c1) sat [p,  R, G, q,a]"
proof -  
  assume
    a0:"(\<forall>s \<in> p. ((\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (c1 s) sat [p, R, G, q,a]) \<and> 
                 (\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> (c1 s) sat [p, R, G, q,a])))" and    
    a1:"\<forall>s. (Normal s, Normal s) \<in> G" and  
    a2: "(Sta p R) \<and> (Sta q R) \<and> (Sta a R) \<and> Norm R"               
  { 
    fix s
    assume all_DynCom:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"     
    then have a0:"(\<forall>s \<in> p. (\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (c1 s) sat [p, R, G, q,a]))"
      using a0 unfolding com_cvalidity_def by fastforce     
    have "cp \<Gamma>(DynCom c1) s \<inter> assum(p, R) F \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cp \<Gamma> (DynCom c1) s" and a11:"c \<in> assum(p, R) F"
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof - 
      {assume l_f:"snd (last l) \<notin> Fault ` F"       
        have cp:"l!0=(DynCom c1,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" 
          using a10 cp_def c_prod by fastforce
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
             then have c1_valid:"(\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (c1 s') sat [p, R, G, q,a])"
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
             moreover then have "cp \<Gamma> csj ssj \<inter> assum(p, R) F \<subseteq> comm(G, (q,a)) F"
               using a2 com_validity_def cj p1 c1_valid by blast
             moreover then have "l!(Suc j) = (csj, Normal s')" 
               using before_k_all_evnt pair_j cj ssj_normal_s
               by fastforce
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
               using  p1 j_length a10 a11 \<Gamma>1  ssj_normal_s
                     cptn_assum_induct[of \<Gamma> l "DynCom c1" s p R F "Suc j" "c1 s'" s' p]
               by blast                         
             then show ?thesis 
             using a00 a21  a10 \<Gamma>1  j_k j_length l_f
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
            moreover then have "cp \<Gamma> csj ssj \<inter> assum(p, R) F \<subseteq> comm(G, (q,a)) F"
              using a0 com_validity_def cj by blast
            moreover then have "l!(Suc j) = (csj, Normal s')" 
              using before_k_all_evnt pair_j cj ssj_normal_s
              by fastforce
            ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
              using  j_length a10 a11 \<Gamma>1  ssj_normal_s
              cptn_assum_induct[of \<Gamma> l "DynCom c1" s p R F "Suc j" "c1 s'" s' p]
              by blast    
            thus ?thesis       
              using j_length l_f drop_comm a10 \<Gamma>1 cptn_comm_induct[of \<Gamma> l "DynCom c1" s _ "Suc j" G q a F "Suc j"] valid  
              by blast
           qed
         } thus ?thesis by auto 
         qed
       note res = conjI [OF concl concr]}               
       thus ?thesis using  c_prod unfolding comm_def by force qed      
    } thus ?thesis by auto qed 
  } thus ?thesis by (auto simp add: com_validity_def[of \<Gamma>] com_cvalidity_def) 
qed

lemma Guard_sound:
  "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> g, R, G, q,a] \<Longrightarrow>
   \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> g, R, G, q,a] \<Longrightarrow>   
   Sta (p \<inter> g) R \<Longrightarrow> (\<forall>s. (Normal s, Normal s) \<in> G) \<Longrightarrow> Norm R \<Longrightarrow>
    \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> (Guard f g c1) sat [p \<inter> g, R, G, q,a]"
proof -  
  assume
    a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [(p \<inter> g) , R, G, q,a]" and
    a1:"\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> g, R, G, q,a]" and        
    a2: "Sta (p \<inter> g) R" and
    a3: "\<forall>s. (Normal s, Normal s) \<in> G" and
    a4: "Norm R"  
  { 
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"  
    then have a1:"\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> g, R, G, q,a]" 
      using a1 com_cvalidity_def by fastforce
    have "cp \<Gamma> (Guard f g c1)  s \<inter> assum(p \<inter> g, R) F \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cp \<Gamma> (Guard f g c1) s" and a11:"c \<in> assum(p \<inter> g, R) F"
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof - 
      {assume l_f:"snd (last l) \<notin> Fault ` F"       
        have cp:"l!0=((Guard f g c1),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
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
           using a4 pair_j before_k_all_evnt cp env_tran_right a2 assum a00 stability[of "p \<inter> g" R l 0 j j \<Gamma>]
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
             moreover then have "cp \<Gamma> csj ssj \<inter> assum(p \<inter> g, R) F \<subseteq> comm(G, (q,a)) F"
               using a1 com_validity_def cj by blast
             moreover then have "l!(Suc j) = (csj, Normal s')" 
               using before_k_all_evnt pair_j cj ssj_normal_s
               by fastforce
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
               using  j_length a10 a11 \<Gamma>1  ssj_normal_s
                     cptn_assum_induct[of \<Gamma> l " (Guard f g c1)" s "(p \<inter> g)" R F "Suc j" c1 s' "p \<inter> g"]
               by blast                         
             then show ?thesis 
             using a4 a00 a21  a10 \<Gamma>1  j_k j_length l_f
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
             using a4 cp final_exist_component_tran_final env_tran_right final_0 
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
              using a4 pair_j before_k_all_evnt cp env_tran_right a2 assum a00 stability[of "p \<inter> g" R l 0 j j \<Gamma>]
              by force
            then obtain s' where ss:"sj = Normal s' \<and> s'\<in> (p \<inter> g)" by auto 
            then have ssj_normal_s:"ssj = Normal s'" 
              using before_k_all_evnt k_basic pair_j a1
              by (metis (no_types, lifting) IntD2 Pair_inject stepc_Normal_elim_cases(2))               
            have cj:"csj=c1" using k_basic pair_j ss a0
              by (metis (no_types, lifting) fst_conv IntD2 stepc_Normal_elim_cases(2))                              
            moreover have p1:"s' \<in> (p \<inter> g)" using ss by blast 
            moreover then have "cp \<Gamma> csj ssj \<inter> assum((p \<inter> g), R) F \<subseteq> comm(G, (q,a)) F"
              using a1 com_validity_def cj by blast
            moreover then have "l!(Suc j) = (csj, Normal s')" 
              using before_k_all_evnt pair_j cj ssj_normal_s
              by fastforce
            ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
              using  j_length a10 a11 \<Gamma>1  ssj_normal_s
              cptn_assum_induct[of \<Gamma> l "(Guard f g c1)" s "(p \<inter> g)" R F "Suc j" c1 s' "(p \<inter> g)"]
              by blast    
            thus ?thesis       
              using j_length l_f drop_comm a10 \<Gamma>1 cptn_comm_induct[of \<Gamma> l "(Guard f g c1)" s _ "Suc j" G q a F "Suc j"] valid  
              by blast
           qed
         } thus ?thesis by auto 
         qed
       note res = conjI [OF concl concr]}               
       thus ?thesis using  c_prod unfolding comm_def by force qed      
    } thus ?thesis by auto qed 
  } thus ?thesis by (simp add: com_validity_def[of \<Gamma>] com_cvalidity_def) 
qed


lemma Guarantee_sound:
  "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [(p \<inter> g),  R, G, q,a] \<Longrightarrow>
   \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [(p \<inter> g), R, G, q,a] \<Longrightarrow>  
   Sta p R \<Longrightarrow> 
   f\<in>F \<Longrightarrow>
   (\<forall>s. (Normal s, Normal s) \<in> G) \<Longrightarrow> Norm R \<Longrightarrow>
   \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> (Guard f g c1) sat [p, R, G, q,a]"
proof -  
  assume
    a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> g, R, G, q,a]" and
    a1:"\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> g, R, G, q,a]" and      
    a2: "Sta p R" and
    a3: "(\<forall>s. (Normal s, Normal s) \<in> G)" and
    a4: "f\<in>F" and
    a5: "Norm R"    
  { 
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"  
    then have a1:"\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> g, R, G, q,a]" 
      using a1 com_cvalidity_def by fastforce
    have "cp \<Gamma> (Guard f g c1)  s \<inter> assum(p, R) F \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cp \<Gamma> (Guard f g c1) s" and a11:"c \<in> assum(p, R) F"
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof - 
      {assume l_f:"snd (last l) \<notin> Fault ` F"       
        have cp:"l!0=((Guard f g c1),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
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
           using a5  pair_j before_k_all_evnt cp env_tran_right a2 assum a00 stability[of p R l 0 j j \<Gamma>]
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
             moreover then have "cp \<Gamma> csj ssj \<inter> assum((p \<inter> g), R) F \<subseteq> comm(G, (q,a)) F"
               using a1 com_validity_def cj by blast
             moreover then have "l!(Suc j) = (csj, Normal s')" 
               using before_k_all_evnt pair_j cj ssj_normal_s
               by fastforce
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
               using  j_length a10 a11 \<Gamma>1  ssj_normal_s
                     cptn_assum_induct[of \<Gamma> l " (Guard f g c1)" s "p" R F "Suc j" c1 s' "(p \<inter> g)"]
               by blast                         
              then show ?thesis 
              using a3 a00 a21  a10 \<Gamma>1  j_k j_length l_f
               cptn_comm_induct[of \<Gamma> l "(Guard f g c1)" s _ "Suc j" G q a F k]
              unfolding Satis_def by fastforce                         
            qed            
          qed
         } note p1=this
         {assume "s' \<in> (Collect (not (set_fun g)))"
          then have "s'\<notin>g" by fastforce
          then have csj_skip:"csj= Skip \<and> ssj=Fault f" using k_basic ss pair_j 
            by (meson Pair_inject stepc_Normal_elim_cases(2))
          then have "snd (last l) = Fault f" using pair_j
          proof -
            have "j = k"
              by (metis (no_types) a5 Suc_leI pair_j csj_skip 
                  a00 a21 before_k_all_evnt cp env_tran_right 
                  le_eq_less_or_eq only_one_component_tran_j)
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
             using a5 cp final_exist_component_tran_final env_tran_right final_0 
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
             using a5 pair_j before_k_all_evnt cp env_tran_right a2 assum a00 stability[of p R l 0 j j \<Gamma>]
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
             moreover then have "cp \<Gamma> csj ssj \<inter> assum((p \<inter> g), R) F \<subseteq> comm(G, (q,a)) F"
               using a1 com_validity_def cj by blast
             moreover then have "l!(Suc j) = (csj, Normal s')" 
               using before_k_all_evnt pair_j cj ssj_normal_s
               by fastforce
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
               using  j_length a10 a11 \<Gamma>1  ssj_normal_s
               cptn_assum_induct[of \<Gamma> l "(Guard f g c1)" s "p" R F "Suc j" c1 s' "(p \<inter> g)"]
               by blast                 
            then have ?thesis       
              using j_length l_f drop_comm a10 \<Gamma>1 cptn_comm_induct[of \<Gamma> l "(Guard f g c1)" s _ "Suc j" G q a F "Suc j"] valid  
              by blast
           }note left=this        
           {
            assume "s' \<in> (Collect (not (set_fun g)))"
            then have "s'\<notin>g" by fastforce
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
  } thus ?thesis by (simp add: com_validity_def[of \<Gamma>] com_cvalidity_def) 
qed

lemma WhileNone:   
   "\<Gamma>\<turnstile>\<^sub>c (While b c1, s1) \<rightarrow> (LanguageCon.com.Skip, t1) \<Longrightarrow>   
    (\<Gamma>, (Skip, t1) # xsa) \<in> cptn \<Longrightarrow>  
    \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> b,R, G, p,a] \<Longrightarrow>
    Sta p R \<Longrightarrow>
    Sta (p \<inter> (-b)) R \<Longrightarrow>
    Sta a R \<Longrightarrow>
    (\<forall>s. (Normal s, Normal s) \<in> G) \<Longrightarrow>            
    (\<Gamma>, (While b c1, s1) # (LanguageCon.com.Skip, t1) # xsa) \<in> assum (p, R) F \<Longrightarrow> 
    (\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p , R, G, q,a]) \<Longrightarrow> 
    Norm R \<Longrightarrow>
    (\<Gamma>, (While b c1, s1) # (LanguageCon.com.Skip, t1) # xsa) \<in> comm (G,(p \<inter> (-b)),a) F"
proof -
  assume a0:"\<Gamma>\<turnstile>\<^sub>c (While b c1, s1) \<rightarrow> (LanguageCon.com.Skip, t1)" and
         a1:"(\<Gamma>, (Skip, t1) # xsa) \<in> cptn" and
         a2:" \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> b,R, G, p,a]" and
         a3:"Sta p R" and
         a4:"Sta (p \<inter> (-b)) R" and
         a5:"Sta a R" and
         a6:"\<forall>s. (Normal s, Normal s) \<in> G" and
         a7:"(\<Gamma>, (While b c1, s1) # (LanguageCon.com.Skip, t1) # xsa) \<in> assum (p, R) F" and
         a8:"(\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p , R, G, q,a])" and
         a9: "Norm R"
  obtain s1' where s1N:"s1=Normal s1' \<and> s1'\<in>p" using a7 unfolding assum_def by fastforce
  then have s1_t1:"s1'\<notin> b \<and> t1=s1" using a0
    using LanguageCon.com.distinct(5) prod.inject 
    by (fastforce elim:stepc_Normal_elim_cases(7))
  then have t1_Normal_post:"t1\<in> Normal ` (p \<inter> (-b))"
    using s1N by fastforce
  also have "(\<Gamma>, (While b c1, s1) # (LanguageCon.com.Skip, t1) # xsa)\<in>cptn"
    using a1 a0 cptn.simps by fastforce
  ultimately have assum_skip:
    "(\<Gamma>,(LanguageCon.com.Skip, t1) # xsa) \<in> assum (( p \<inter> (-b)), R) F"
    using a1 a7 tl_of_assum_in_assum1 t1_Normal_post by fastforce
  have skip_comm:"(\<Gamma>,(LanguageCon.com.Skip, t1) # xsa) \<in> 
               comm (G,(( p \<inter> (-b)),a)) F" 
  proof- 
    have "\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Skip sat [( p \<inter> (-b)), R, G, ( p \<inter> (-b)),a]"
      using Skip_sound[of "(p \<inter> - b)"] a9 a4 a6 by blast
    thus ?thesis
      using assum_skip cp_def a1 a8 unfolding com_cvalidity_def com_validity_def
      by fastforce
  qed    
  have G_ref:"(Normal s1', Normal s1')\<in>G" using a6 by fastforce
  thus ?thesis using skip_comm ctran_in_comm[of s1'] s1N s1_t1 by blast
qed 

lemma while1:
   "(\<Gamma>, ((c, Normal s1) # xs1)) \<in> cptn_mod \<Longrightarrow>    
    s1 \<in> b \<Longrightarrow>
    xsa = map (lift (While b c)) xs1 \<Longrightarrow>
    \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c sat [p \<inter> b,R, G, p,a] \<Longrightarrow>    
    (\<Gamma>, (While b c, Normal s1) #
        (Seq c (LanguageCon.com.While b c), Normal s1) # xsa)
       \<in> assum (p, R) F \<Longrightarrow>               
    \<forall>s. (Normal s, Normal s) \<in> G \<Longrightarrow> Norm R \<Longrightarrow>
     (\<Gamma>, (LanguageCon.com.While b c, Normal s1) #
         (LanguageCon.com.Seq c (LanguageCon.com.While b c), Normal s1) # xsa)
    \<in> comm (G, p\<inter>(-b), a) F"
proof -
assume   
  a0:"(\<Gamma>, ((c, Normal s1) # xs1)) \<in> cptn_mod" and
  a1:"s1 \<in> b" and
  a2:"xsa = map (lift (While b c)) xs1" and
  a3:"\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c sat [p \<inter> b,R, G, p,a]" and
  a4:"(\<Gamma>, (While b c, Normal s1) #
        (Seq c (While b c), Normal s1) # xsa)
       \<in> assum (p, R) F" and  
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
    using a2 cptn_eq_cptn_mod lift_is_cptn a0 by fastforce
  then have cptn_seq:"(\<Gamma>,(Seq c (While b c), Normal s1) # xsa) \<in>cptn" 
    using seq_map by auto
  then have "(\<Gamma>, (While b c, Normal s1) # (Seq c (While b c), Normal s1) # xsa) \<in> cptn"
    using step by (simp add: cptn.CptnComp) 
  then have assum_seq:"(\<Gamma>,(Seq c (While b c), Normal s1) # xsa)\<in>assum (p, R) F"
    using a4 tl_of_assum_in_assum1 s1_collect_p by fastforce
  have cp_c:"(\<Gamma>, ((c, Normal s1) # xs1)) \<in> (cp \<Gamma> c (Normal s1))"
    using a0[THEN cptn_if_cptn_mod] unfolding cp_def by fastforce
  also have cp_seq:"(\<Gamma>, (Seq c (While b c), Normal s1) # xsa) \<in> (cp \<Gamma> (Seq c (While b c)) (Normal s1))"
    using cptn_seq unfolding cp_def by fastforce
  ultimately have "(\<Gamma>, ((c, Normal s1) # xs1)) \<in> assum(p,R) F"  
    using assum_map assum_seq seq_map by fastforce  
  then have "(\<Gamma>, ((c, Normal s1) # xs1)) \<in> assum((p \<inter> b),R) F"
    unfolding assum_def using s1_collect_p by fastforce
  then have "(\<Gamma>, ((c, Normal s1) # xs1)) \<in> comm(G,(p,a)) F"
    using a3 cp_c unfolding com_validity_def by fastforce
  then have "(\<Gamma>, (Seq c (While b c), Normal s1) # xsa) \<in> comm(G,(p,a)) F"
    using cp_seq cp_c comm_map seq_map by fastforce
  then have "(\<Gamma>, (While b c, Normal s1) # (Seq c (While b c), Normal s1) # xsa) \<in> comm(G,(p,a)) F"
    using G_ref ctran_in_comm by fastforce
  also have "\<not> final (last ((While b c, Normal s1) # (Seq c (While b c), Normal s1) # xsa))"
    using seq_map unfolding final_def lift_def  by (simp add: case_prod_beta' last_map)  
  ultimately show ?thesis using not_final_in_comm[of \<Gamma>] by blast
qed

lemma while2:
   " (\<Gamma>, (While b c, Normal s1) #
         (Seq c (While b c), Normal s1) # xsa) \<in>cptn \<Longrightarrow>
    (\<Gamma>, (c, Normal s1) # xs1) \<in> cptn_mod \<Longrightarrow>
    fst (last ((c, Normal s1) # xs1)) = LanguageCon.com.Skip \<Longrightarrow>
    s1 \<in> b \<Longrightarrow>
    xsa = map (lift (While b c)) xs1 @
    (While b c, snd (last ((c, Normal s1) # xs1))) # ys \<Longrightarrow>
    (\<Gamma>, (While b c, snd (last ((c, Normal s1) # xs1))) # ys)
      \<in> cptn_mod \<Longrightarrow>
     (\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c sat [p \<inter> b, R, G, p,a] \<Longrightarrow>    
       (\<Gamma>, (While b c, snd (last ((c, Normal s1) # xs1))) # ys)
         \<in> assum (p, R) F \<Longrightarrow>
       (\<Gamma>, (While b c, snd (last ((c, Normal s1) # xs1))) # ys)
          \<in> comm (G, p \<inter> (-b), a) F) \<Longrightarrow>
    \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c sat [ p \<inter> b, R, G, p,a] \<Longrightarrow>
    (\<Gamma>, (While b c, Normal s1) #
      (Seq c (While b c), Normal s1) # xsa)
      \<in> assum (p, R) F \<Longrightarrow>
     \<forall>s. (Normal s,Normal s) \<in> G  \<Longrightarrow>
     Norm R \<Longrightarrow>
    (\<Gamma>, (While b c, Normal s1) #
         (Seq c (While b c), Normal s1) # xsa)
      \<in> comm (G,( p \<inter> (-b), a)) F"
proof -
assume a00:"(\<Gamma>, (While b c, Normal s1) #
         (Seq c (While b c), Normal s1) # xsa) \<in>cptn" and
       a0:"(\<Gamma>, (c, Normal s1) # xs1) \<in> cptn_mod" and
       a1:" fst (last ((c, Normal s1) # xs1)) = LanguageCon.com.Skip" and
       a2:"s1 \<in> b" and
       a3:"xsa = map (lift (While b c)) xs1 @
            (While b c, snd (last ((c, Normal s1) # xs1))) # ys" and
       a4:"(\<Gamma>, (While b c, snd (last ((c, Normal s1) # xs1))) # ys)
            \<in> cptn_mod" and
       a5:"\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c sat [p \<inter> b, R, G, p,a]" and       
       a6:"(\<Gamma>, (While b c, Normal s1) #
               (Seq c (While b c), Normal s1) # xsa)
             \<in> assum (p, R) F" and
       a7:"(\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c sat [p \<inter> b, R, G, p,a] \<Longrightarrow>    
           (\<Gamma>, (While b c, snd (last ((c, Normal s1) # xs1))) # ys)
             \<in> assum (p, R) F \<Longrightarrow>
           (\<Gamma>, (While b c, snd (last ((c, Normal s1) # xs1))) # ys)
             \<in> comm (G,p \<inter> (-b), a) F)" and
       a8:"\<forall>s. (Normal s, Normal s) \<in> G"   and
       a9: "Norm R" 
  let ?l= "(While b c, Normal s1) #
           (Seq c (While b c), Normal s1) # xsa"
  let ?sub_l="((While b c, Normal s1) # 
                 (Seq c (While b c), Normal s1) # 
                 map (lift (While b c)) xs1)"
  {
  assume final_not_fault:"snd (last ?l) \<notin> Fault ` F"
  have a0:"(\<Gamma>, (c, Normal s1) # xs1) \<in> cptn"
    using cptn_if_cptn_mod using a0 by auto
  have a4:"(\<Gamma>, (While b c, snd (last ((c, Normal s1) # xs1))) # ys) \<in> cptn" 
    using cptn_if_cptn_mod using a4 by auto
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
    using a2 cptn_eq_cptn_mod lift_is_cptn a0 by fastforce
  then have cptn_seq:"(\<Gamma>,(Seq c (While b c), Normal s1) # map (lift (While b c)) xs1) \<in>cptn" 
    using seq_map by auto
  then have "(\<Gamma>, (While b c, Normal s1) # 
                 (Seq c (While b c), Normal s1) # 
                  map (lift (While b c)) xs1) \<in> cptn"
    using step by (simp add: cptn.CptnComp) 
  also have "(\<Gamma>, (While b c, Normal s1) #
                 (Seq c (While b c), Normal s1) #
                  map (lift (While b c)) xs1)
          \<in> assum (p, R) F"
    using a6 a3 sub_assum by force 
  ultimately have assum_seq:"(\<Gamma>,(Seq c (While b c), Normal s1)  # 
                       map (lift (While b c)) xs1) \<in> assum (p, R) F"
    using a6 tl_of_assum_in_assum1 s1_collect_p 
          tl_of_assum_in_assum   by fastforce
  have cp_c:"(\<Gamma>, ((c, Normal s1) # xs1)) \<in> (cp \<Gamma> c (Normal s1))"
    using a0 unfolding cp_def by fastforce
  also have cp_seq:"(\<Gamma>, (Seq c (While b c), Normal s1) # map (lift (While b c)) xs1) \<in> (cp \<Gamma> (Seq c (While b c)) (Normal s1))"
    using cptn_seq unfolding cp_def by fastforce
  ultimately have "(\<Gamma>, ((c, Normal s1) # xs1)) \<in> assum(p,R) F"  
    using assum_map assum_seq seq_map by fastforce  
  then have "(\<Gamma>, ((c, Normal s1) # xs1)) \<in> assum((p \<inter> b),R) F"
    unfolding assum_def using s1_collect_p by fastforce
  then have c_comm:"(\<Gamma>, ((c, Normal s1) # xs1)) \<in> comm(G,(p,a)) F"
    using a5 cp_c unfolding com_validity_def by fastforce
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
      using final_not_fault a3 a00 last_not_F[of \<Gamma> ?l F]  by fast
    thus ?thesis using last_while2 last_while1 seq_map
      by (metis (no_types) Cons_lift_append  a3 diff_Suc_1 last_length length_Cons lessI nth_Cons_Suc nth_append)
  qed
  then have last_c_normal:"snd (last ( (c,Normal s1)#xs1)) \<in> Normal ` (p)"
    using c_comm a1 unfolding comm_def final_def by fastforce    
  then obtain sl where sl:"snd (last ( (c,Normal s1)#xs1)) = Normal sl" by fastforce
  have while_comm:"(\<Gamma>, (While b c, snd (last ((c, Normal s1) # xs1))) # ys) \<in> comm(G,(p\<inter>(-b),a)) F"
  proof -
    have assum_while: "(\<Gamma>, (While b c, snd (last ((c, Normal s1) # xs1))) # ys)
             \<in> assum (p, R) F"
      using last_c_normal a3 a6 sub_assum_r[of \<Gamma> ?sub_l "(While b c, snd (last ((c, Normal s1) # xs1)))"  ys p R F p] 
      by fastforce
    thus ?thesis using a5 a7 by fastforce
  qed      
  have "sl\<in>p" using last_c_normal sl by fastforce
  then have G1_ref:"(Normal sl, Normal sl)\<in>G" using a8 by auto
  also have "snd (last ?sub_l) = Normal sl"
    using last_while1 last_while2 sl by fastforce
  ultimately have ?thesis 
    using a9 a00 a3 sl while_comm comm_union[OF comm_while]  
    by fastforce    
  } note p1 =this
  {
    assume final_not_fault:"\<not> (snd (last ?l) \<notin> Fault ` F)"
    then have ?thesis unfolding comm_def by fastforce
  } thus ?thesis using p1 by fastforce
qed

lemma while3:
   "(\<Gamma>, (c, Normal s1) # xs1) \<in> cptn_mod \<Longrightarrow>    
    fst (last ((c, Normal s1) # xs1)) = Throw \<Longrightarrow>
    s1 \<in> b \<Longrightarrow>
    snd (last ((c, Normal s1) # xs1)) = Normal sl \<Longrightarrow>
    (\<Gamma>, (Throw, Normal sl) # ys) \<in> cptn_mod   \<Longrightarrow>
    \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c sat [p \<inter> b,R, G, p,a] \<Longrightarrow>    
    (\<Gamma>, (While b c, Normal s1) #
         (Seq c (While b c), Normal s1) #  
         (map (lift (While b c)) xs1 @
           (Throw, Normal sl) # ys))
       \<in> assum (p, R) F \<Longrightarrow>    
    (\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]) \<Longrightarrow>      
     Sta p R \<Longrightarrow>
     Sta a R \<Longrightarrow> \<forall>s. (Normal s, Normal s) \<in> G \<Longrightarrow> 
     Norm R \<Longrightarrow>
    (\<Gamma>, (While b c, Normal s1) #
         (Seq c (While b c), Normal s1) #          
         ((map (lift (While b c)) xs1 @
           (Throw, Normal sl) # ys))) \<in> comm (G, p\<inter> (-b), a) F
"
proof -
assume a0:"(\<Gamma>, (c, Normal s1) # xs1) \<in> cptn_mod" and
       a1:"fst (last ((c, Normal s1) # xs1)) = Throw" and
       a2:"s1 \<in> b" and
       a3:"snd (last ((c, Normal s1) # xs1)) = Normal sl" and
       a4:"(\<Gamma>, (Throw, Normal sl) # ys) \<in> cptn_mod" and
       a5:"\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c sat [p \<inter> b, R, G, p,a]" and
       a6:"(\<Gamma>, (While b c, Normal s1) #
           (Seq c (While b c), Normal s1) #  
           (map (lift (While b c)) xs1 @
             (Throw, Normal sl) # ys))
           \<in> assum (p, R) F" and      
       a7: "Sta p R" and
       a8: "Sta a R" and
       a9: "(\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a])" and
       a10:"\<forall>s. (Normal s,Normal s) \<in> G" and
       a11:"Norm R"
  have a0:"(\<Gamma>, (c, Normal s1) # xs1) \<in> cptn"
    using cptn_if_cptn_mod using a0 by auto
  have a4:"(\<Gamma>, (Throw, Normal sl) # ys) \<in> cptn" 
    using cptn_if_cptn_mod using a4 by auto
  have seq_map:"(Seq c (While b c), Normal s1) # map (lift (While b c)) xs1=
           map (lift (While b c)) ((c,Normal s1)#xs1)"
  using a2 unfolding lift_def by fastforce
  have step:"\<Gamma>\<turnstile>\<^sub>c(While b c,Normal s1) \<rightarrow> (Seq c (While b c),Normal s1)" using a2
    WhileTruec by fastforce
  have s1_normal:"s1\<in>p \<and> s1 \<in> b " using a6 a2 unfolding assum_def by fastforce
  then have G_ref:"(Normal s1, Normal s1)\<in>G" using a10 by auto
  have s1_collect_p: "Normal s1\<in> Normal ` (p \<inter> b)" using s1_normal by fastforce
  have "(\<Gamma>, map (lift (While b c)) ((c,Normal s1)#xs1))\<in>cptn" 
    using a2 cptn_eq_cptn_mod lift_is_cptn a0 by fastforce
  then have cptn_seq:"(\<Gamma>,(Seq c (While b c), Normal s1) # map (lift (While b c)) xs1) \<in>cptn" 
    using seq_map by auto
  then have cptn:"(\<Gamma>, (While b c, Normal s1) # 
                 (Seq c (While b c), Normal s1) # 
                  map (lift (While b c)) xs1) \<in> cptn"
    using step by (simp add: cptn.CptnComp) 
  also have "(\<Gamma>, (LanguageCon.com.While b c, Normal s1) #
         (LanguageCon.com.Seq c (LanguageCon.com.While b c), Normal s1) #
         map (lift (LanguageCon.com.While b c)) xs1)
          \<in> assum (p, R) F"
    using a6 sub_assum by force 
  ultimately have assum_seq:"(\<Gamma>,(Seq c (While b c), Normal s1)  # 
                       map (lift (While b c)) xs1) \<in> assum (p, R) F"
    using a6 tl_of_assum_in_assum1 s1_collect_p 
          tl_of_assum_in_assum  by fastforce
  have cp_c:"(\<Gamma>, ((c, Normal s1) # xs1)) \<in> (cp \<Gamma> c (Normal s1))"
    using a0 unfolding cp_def by fastforce
  also have cp_seq:"(\<Gamma>, (Seq c (While b c), Normal s1) # map (lift (While b c)) xs1) \<in> (cp \<Gamma> (Seq c (While b c)) (Normal s1))"
    using cptn_seq unfolding cp_def by fastforce
  ultimately have "(\<Gamma>, ((c, Normal s1) # xs1)) \<in> assum(p,R) F"  
    using assum_map assum_seq seq_map by fastforce  
  then have "(\<Gamma>, ((c, Normal s1) # xs1)) \<in> assum((p \<inter> b),R) F"
    unfolding assum_def using s1_collect_p by fastforce
  then have c_comm:"(\<Gamma>, ((c, Normal s1) # xs1)) \<in> comm(G,(p,a)) F"
    using a5 cp_c unfolding com_validity_def by fastforce
  then have "(\<Gamma>, (Seq c (While b c), Normal s1) # map (lift (While b c)) xs1) \<in> comm(G,(p,a)) F"
    using cp_seq cp_c comm_map seq_map by fastforce
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
    have assum_throw: "(\<Gamma>, (Throw, Normal sl) # ys) \<in> assum (a,R) F"
      using sl_a a6 sub_assum_r[of _ "(LanguageCon.com.While b c, Normal s1) #
         (LanguageCon.com.Seq c (LanguageCon.com.While b c), Normal s1) #
         map (lift (LanguageCon.com.While b c)) xs1" "(Throw, Normal sl)" ] 
      by fastforce
    also have "(\<Gamma>,(Throw, Normal sl) # ys) \<in> cp \<Gamma> Throw (Normal sl)" 
      unfolding cp_def using a4 by fastforce
    ultimately show ?thesis using Throw_sound[of a R G \<Gamma>] a10 a8 a9 a11 
      unfolding com_cvalidity_def com_validity_def by fast
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
    \<in> cptn" using cptn a4  a0 a1 a3 a4 cptn_eq_cptn_mod_set cptn_mod.CptnModWhile3 s1_normal by fastforce
  show ?thesis using a0 a11  comm_union[OF comm_while throw_comm p1 G cptn] by auto       
qed


inductive_cases stepc_elim_cases_while_throw [cases set]:
 "\<Gamma>\<turnstile>\<^sub>c(While b c, s) \<rightarrow> (Throw, t)"

lemma WhileSound_aux:
 "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> b, R, G, p,a] \<Longrightarrow>
  Sta p R \<Longrightarrow>
  Sta  (p \<inter> (-b)) R \<Longrightarrow> 
  Sta a R \<Longrightarrow>    
  (\<Gamma>,x)\<in> cptn_mod \<Longrightarrow> 
  \<forall>s. (Normal s, Normal s) \<in> G \<Longrightarrow>
  Norm R \<Longrightarrow>
  \<forall>s xs. x = ((While b c1),s)#xs \<longrightarrow> 
     (\<Gamma>,x)\<in>assum(p,R) F \<longrightarrow> 
     (\<Gamma>,x) \<in> comm (G,(( p \<inter> (-b)),a)) F"
proof -
  assume a0: "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> b, R, G, p,a] " and
         a1: "Sta p R" and
         a2: "Sta  (p \<inter> (-b)) R" and
         a3: "Sta a R" and
         a4: "(\<Gamma>,x)\<in> cptn_mod" and
         a5: "\<forall>s. (Normal s, Normal s) \<in> G" and
         a6: "Norm R"
   {fix xs s 
   assume while_xs:"x=((While b c1),s)#xs" and
          x_assum:"(\<Gamma>,x)\<in>assum(p,R) F"
   have "(\<Gamma>,x) \<in> comm (G,(( p \<inter> (-b)),a)) F"
   using a4 a0  while_xs x_assum
   proof (induct arbitrary: xs s c1 rule:cptn_mod.induct)
     case (CptnModOne  \<Gamma> C s1) thus ?case 
       using CptnModOne unfolding comm_def final_def
       by auto
   next
     case (CptnModEnv  \<Gamma> C s1 t1 xsa) 
     then have c_while:"C = While b c1" by fastforce
     have "(\<Gamma>, (C, t1) # xsa) \<in> assum (p, R) F \<longrightarrow>
                (\<Gamma>, (C, t1) # xsa) \<in> comm (G, p \<inter> (-b), a) F"  
     using CptnModEnv by fastforce  
     moreover have"(\<Gamma>,(C, s1)#(C, t1) # xsa) \<in> cptn_mod"
       using CptnModEnv(1,2)
       by (simp add: CptnModEnv.hyps(1) CptnModEnv.hyps(2) cptn_mod.CptnModEnv)
     then have  cptn_mod:"(\<Gamma>,(C, s1)#(C, t1) # xsa) \<in> cptn"
       using cptn_eq_cptn_mod_set by blast      
     then have "(\<Gamma>, (C, t1) # xsa) \<in> assum (p, R) F"   
       using tl_of_assum_in_assum CptnModEnv(6) a1 a2 a3 a4 a5 a6
       by blast
     ultimately have "(\<Gamma>, (C, t1) # xsa) \<in> comm (G, p \<inter> (-b), a) F"
       by auto
     also have " \<not> (\<Gamma>\<turnstile>\<^sub>c((C,s1))  \<rightarrow> ((C,t1)))" 
     proof 
       assume step:"\<Gamma>\<turnstile>\<^sub>c (C, s1) \<rightarrow> (C, t1)"
       show False 
       proof (cases s1)
         case (Normal s1') thus ?thesis 
           using step step_change_p_or_eq_Ns redex.simps(6) LanguageCon.com.distinct(91) c_while
           by fastforce
       next
         case Abrupt thus ?thesis 
           using step c_while  prod.inject stepc_elim_cases(7) xstate.distinct(1) 
           by fastforce
       next
         case Fault thus ?thesis
           using step c_while  prod.inject stepc_elim_cases(7) xstate.distinct(1) 
           by fastforce
       next
         case Stuck thus ?thesis
           using step c_while  prod.inject stepc_elim_cases(7) xstate.distinct(1) 
           by fastforce
       qed
     qed
     ultimately show ?case 
       using cptn_mod etran_in_comm by blast
   next 
     case (CptnModSkip \<Gamma> C s1 t1 xsa) 
     then have "C=While b c1" by auto
     also have "(\<Gamma>, (LanguageCon.com.Skip, t1) # xsa) \<in> cptn"
       using cptn_eq_cptn_mod_set CptnModSkip(3) by fastforce
     thus ?case using WhileNone CptnModSkip a1 a2 a3 a4 a5 a6 by blast
   next
     case (CptnModThrow  \<Gamma> C s1 t1 xsa) 
     then have "C = While b c1" by auto 
       thus ?case using stepc_elim_cases_while_throw CptnModThrow(1) 
       by blast
   next 
     case (CptnModWhile1  \<Gamma> c s1 xs1 b1 xsa zs) 
     then have "b=b1 \<and> c=c1 \<and> s=Normal s1" by auto      
     thus ?case
     using a6 a4 a5 CptnModWhile1 while1[of \<Gamma>] by blast
   next 
     case (CptnModWhile2 \<Gamma> c s1 xs1 b1 xsa ys zs)
     then have a00: "(\<Gamma>, (While b c, Normal s1) #
         (Seq c (While b c), Normal s1) # xsa)\<in>cptn_mod" 
       using cptn_mod.CptnModWhile2 by fast note pp1 = this[THEN cptn_if_cptn_mod]  
     then have eqs:"b=b1 \<and> c=c1 \<and> s=Normal s1"using CptnModWhile2 by auto
     thus ?case using a6 pp1 a4 a5 CptnModWhile2 while2[of \<Gamma> b c s1 xsa xs1 ys F p R G a] 
         by fastforce
   next
     case (CptnModWhile3 \<Gamma> c s1 xs1 b1 sl ys zs)  
     then have eqs:"b=b1 \<and> c=c1 \<and> s=Normal s1" by auto 
     then have "(\<Gamma>, (While b c, Normal s1) #
         (Seq c (While b c), Normal s1) #          
         ((map (lift (While b c)) xs1 @
           (Throw, Normal sl) # ys))) \<in> comm (G, p\<inter>(-b), a) F"        
       using a6 a1 a3 a4 a5 CptnModWhile3 while3[of \<Gamma> c s1 xs1 b sl ys F p R G a] 
       by fastforce   
     thus ?case using eqs CptnModWhile3 by auto
   qed (auto)
  }
  then show ?thesis by auto    
qed



lemma While_sound: 
      "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> b, R, G, p,a] \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> b, R, G, p,a] \<Longrightarrow>       
       Sta p R \<Longrightarrow>     
       Sta (p \<inter> (-b)) R \<Longrightarrow> Sta a R \<Longrightarrow> \<forall>s. (Normal s, Normal s) \<in> G \<Longrightarrow> Norm R \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> (While b c1) sat [p, R, G, p \<inter> (-b),a]"
proof -  
  assume
    a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> b, R, G, p,a]" and
    a1:"\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> b, R, G, p,a]" and    
    a2: "Sta p R" and
    a3: "Sta (p \<inter> (-b)) R" and
    a4: "Sta a R" and
    a5: "\<forall>s. (Normal s, Normal s) \<in> G" and
    a6: "Norm R"   
  { 
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"  
    then have a1:"\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> b, R, G, p,a]" 
      using a1 com_cvalidity_def by fastforce
    have "cp \<Gamma> (While b c1)  s \<inter> assum(p, R) F \<subseteq> comm(G, (p \<inter> (-b),a)) F"
    proof-
      {fix c     
      assume a10:"c \<in> cp \<Gamma> (While b c1) s" and a11:"c \<in> assum(p, R) F"
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have cp:"l!0=((While b c1),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce      
      have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast
      obtain xs where "l=((While b c1),s)#xs" using cp
      proof -
        assume a1: "\<And>xs. l = (LanguageCon.com.While b c1, s) # xs \<Longrightarrow> thesis"
        have "[] \<noteq> l"
          using cp cptn.simps by auto
        then show ?thesis
          using a1 by (metis (full_types) SmallStepCon.nth_tl cp)
      qed 
      moreover have "(\<Gamma>,l)\<in>cptn_mod" using cp cptn_eq_cptn_mod_set by fastforce
      ultimately have "c \<in> comm(G, (p \<inter> (-b),a)) F"
      using a1 a2 a3 a4   WhileSound_aux a11 \<Gamma>1 a5 a6
        by blast
      } thus ?thesis by auto qed
  }
  thus ?thesis by (simp add: com_validity_def[of \<Gamma>] com_cvalidity_def)  
qed


lemma Conseq_sound:
  "(\<forall>s\<in> p.
       \<exists>p' R' G' q' a' I'.
          s \<in> p' \<and>
          R \<subseteq> R' \<and>            
          G' \<subseteq> G \<and>             
          q' \<subseteq> q \<and>
          a' \<subseteq> a \<and>
          \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p',R', G', q',a'] \<and> 
          \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> P sat [p', R', G', q',a']) \<Longrightarrow>
  \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> P sat [p,R, G, q,a]" 
proof -
  assume 
  a0: "(\<forall>s\<in> p.
       \<exists>p' R' G' q' a' I'.
          s \<in> p' \<and>
          R \<subseteq> R' \<and>            
          G' \<subseteq> G \<and>             
          q' \<subseteq> q \<and>
          a' \<subseteq> a \<and>
          \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p',R', G', q',a'] \<and> 
          \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> P sat [p', R', G', q',a'])"
  {
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"
    have "cp \<Gamma> P  s \<inter> assum(p, R) F \<subseteq> comm(G, (q,a)) F"
    proof -
    {
      fix c
      assume a10:"c \<in> cp \<Gamma> P s" and a11:"c \<in> assum(p, R) F"
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have cp:"l!0=(P,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
      have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast 
      obtain xs where "l=(P,s)#xs" using cp
      proof -
        assume a1: "\<And>xs. l = (P, s) # xs \<Longrightarrow> thesis"
        have "[] \<noteq> l"
          using cp cptn.simps by auto
        then show ?thesis
          using a1 by (metis (full_types) SmallStepCon.nth_tl cp)
      qed
      obtain ns where s:"(s = Normal ns)" using a10 a11 unfolding assum_def cp_def by fastforce
      then have "ns \<in> p" using a10 a11 unfolding assum_def cp_def by fastforce
      then have ns:"ns\<in>p" by auto
      then have
      "\<forall>s. s \<in> p \<longrightarrow> (\<exists>p' R' G' q' a' . (s\<in>p') \<and>
        R \<subseteq> R' \<and>            
        G' \<subseteq> G \<and>             
        q' \<subseteq> q \<and>
        a' \<subseteq> a \<and>
        (\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p',R', G', q',a']) \<and> 
        \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> P sat [p', R', G', q',a'])" using a0 by auto
      then have 
       "ns \<in> p \<longrightarrow> (\<exists>p' R' G' q' a'. (ns \<in> p' ) \<and>
        R \<subseteq> R' \<and>            
        G' \<subseteq> G \<and>             
        q' \<subseteq> q \<and>
        a' \<subseteq> a \<and>
        (\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p',R', G', q',a']) \<and> 
        \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> P sat [p', R', G', q',a'])" apply (rule allE) by auto     
     then obtain p' R' G' q' a' where
     rels:
       "ns \<in> p' \<and>
        R \<subseteq> R' \<and>            
        G' \<subseteq> G \<and>             
        q' \<subseteq> q \<and>
        a' \<subseteq> a \<and>        
        \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> P sat [p', R', G', q',a']" using ns by auto
      then have "s \<in>  Normal ` p'" using s by fastforce
      then have "(\<Gamma>,l) \<in> assum(p', R') F"
        using a11 rels cp a11 c_prod assum_R_R'[of \<Gamma> l p R F p' R'] 
        by fastforce
      then have "(\<Gamma>,l) \<in> comm(G',(q',a')) F" 
        using rels all_call a10 c_prod cp unfolding com_cvalidity_def com_validity_def 
        by blast
      then have "(\<Gamma>,l) \<in> comm(G, (q,a)) F" 
        using c_prod cp comm_conseq[of \<Gamma> l G' q' a' F G q a] rels by fastforce
      then have "c \<in> comm(G, (q,a)) F" using c_prod cp by fastforce
    }                 
    thus ?thesis unfolding comm_def by force qed      
  } thus ?thesis by (simp add: com_validity_def[of \<Gamma>] com_cvalidity_def)  
qed   

lemma Conj_post_sound:
  "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p,R, G, q,a] \<and> 
   \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q,a] \<Longrightarrow> 
   \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p,R, G, q',a'] \<and> 
   \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q',a'] \<Longrightarrow>
  \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> P sat [p,R, G, q \<inter> q' ,a \<inter> a']" 
proof -
assume a0: "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p,R, G, q,a] \<and> 
            \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q,a]" and
       a1: " \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p,R, G, q',a'] \<and> 
             \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q',a']"
{
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"
    with a0 have a0:"cp \<Gamma> P  s \<inter> assum(p, R) F \<subseteq> comm(G, (q,a)) F"
      unfolding com_cvalidity_def com_validity_def by auto
    with a1 all_call have a1:"cp \<Gamma> P  s \<inter> assum(p, R) F \<subseteq> comm(G, (q',a')) F"
      unfolding com_cvalidity_def com_validity_def by auto
    have "cp \<Gamma> P  s \<inter> assum(p, R) F \<subseteq> comm(G, (q\<inter>q',a\<inter>a')) F"
    proof -
    {
      fix c
      assume a10:"c \<in> cp \<Gamma> P s" and a11:"c \<in> assum(p, R) F"
      then have "c \<in> comm(G,(q,a)) F \<and> c \<in> comm(G,(q',a')) F"
        using a0 a1 by auto
      then have  "c\<in>comm(G, (q\<inter>q',a\<inter>a')) F"
        unfolding comm_def by fastforce
    }               
    thus ?thesis unfolding comm_def by force qed      
  } thus ?thesis by (simp add: com_validity_def[of \<Gamma>] com_cvalidity_def)  
qed   

lemma localRG_sound: "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p, R, G, q,a] \<Longrightarrow> \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c sat [p, R, G, q,a]"
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
  case If thus ?case by (simp add: If_sound)
next 
  case Call thus ?case by (simp add: Call_sound)
next
  case Asm thus ?case by (simp add: Asm_sound)
next
  case CallRec thus ?case using CallRec_sound by (simp add: CallRec_sound)
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
qed   


definition ParallelCom :: "('s,'p,'f) rgformula list \<Rightarrow> ('s,'p,'f) par_com"
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
   thus ?thesis using prod step_change_p_or_eq_s_normal a0 by fastforce
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
      using a1 a2 step_change_p_or_eq_s_normal[of \<Gamma> fp fs sp ss] all_env prod_step allP 
      by metis 
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
   length xs=length clist; (\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s; (\<Gamma>,l)\<in>par_assum (p, R) F;
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
         a5: "(\<Gamma>,l)\<in>par_assum (p, R) F" and
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
            using prod_step step_change_p_or_eq_s_normal[of "\<Gamma>" fp fs sp ss] 
          by fastforce
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
                             assum ((Pre (xs ! i')),Rely (xs ! i')) F"
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
   length xs=length clist; (\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s; (\<Gamma>,l)\<in>par_assum (p, R) F;
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
         a5: "(\<Gamma>,l)\<in>par_assum (p, R) F" and
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
     moreover have take_in_ass:"(\<Gamma>, take (Suc (Suc m)) (snd (clist!i))) \<in> assum (Pre(xs!i), Rely(xs!i)) F"     
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
   length xs=length clist; (\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s; (\<Gamma>,l) \<in> par_assum(p, R) F;
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
        a6: "(\<Gamma>,l) \<in> par_assum(p, R) F" and
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
          using P a20 step_change_p_or_eq_s_normal by fastforce                    
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

                                                                                        
lemma four:
  "\<lbrakk>xs\<noteq>[];  \<forall>i<length xs.  R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Guar (xs ! j)))
       \<subseteq>  (Rely (xs ! i));
   (\<Union>j<length xs.  (Guar (xs ! j))) \<subseteq> (G);
   p \<subseteq> (\<Inter>i<length xs.  (Pre (xs ! i)));
   \<forall>i<length xs.
     \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Com (xs ! i) sat [Pre (xs!i),  Rely (xs ! i), Guar (xs ! i), Post (xs ! i),Abr (xs ! i)];
    (\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s; (\<Gamma>,l) \<in> par_assum(p, R) F; Suc i < length l;
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
         a6:"(\<Gamma>,l) \<in> par_assum(p, R) F" and
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
    (\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s; (\<Gamma>,l) \<in> par_assum(p, R) F;
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
         a7:"(\<Gamma>,l) \<in> par_assum(p, R) F"and
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
   have clist_assum:"\<forall>i<length clist. (clist!i) \<in> assum (Pre (xs!i),Rely (xs!i)) F"     
   proof -
   { fix i
     assume i_length:"i<length clist"
     obtain \<Gamma>1 li where clist:"clist!i=(\<Gamma>1,li)" by fastforce    
     then have \<Gamma>eq:"\<Gamma>1=\<Gamma>" 
       using conjoin i_length unfolding conjoin_def same_functions_def by fastforce
     have "(\<Gamma>1,li) \<in> assum (Pre (xs!i),Rely (xs!i)) F"
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
     then have "clist!i \<in> assum (Pre (xs!i),Rely (xs!i)) F" using clist by auto            
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
       assume a10: "(\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s \<and> (\<Gamma>,l) \<in> par_assum(p, R) F"       
       then have c_par_cp:"(\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s" by auto
       have c_par_assum: "(\<Gamma>,l) \<in> par_assum(p, R) F" using a10 by auto
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
    thus ?case using localRG_sound parallel_sound[of xs R G p q a \<Gamma> \<Theta> F] 
      by fast
qed
lemma Conseq':"\<forall>s. s\<in>p \<longrightarrow>
              (\<exists>p' q' a' R' G'. 
                (\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [(p' Z), (R' Z), (G' Z), (q' Z),(a' Z)]) \<and>
                   (\<exists> Z. s\<in>p' Z \<and> (q' Z \<subseteq> q) \<and> (a' Z \<subseteq> a) \<and> (G' Z \<subseteq> G) \<and> (R \<subseteq> R' Z)))
              \<Longrightarrow>
              \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q,a]"
by (rule Conseq) meson

lemma conseq:"\<lbrakk>\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [(p' Z), (R' Z), (G' Z), (q' Z),(a' Z)];
              \<forall>s. s \<in> p \<longrightarrow> (\<exists> Z. s\<in>p' Z \<and> (q' Z \<subseteq> q) \<and> (a' Z \<subseteq> a) \<and> (G' Z \<subseteq> G) \<and> (R \<subseteq> R' Z))\<rbrakk>
              \<Longrightarrow>
               \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q,a]"
by (rule Conseq) meson

lemma conseqPrePost[trans]:
 "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p', R', G', q',a'] \<Longrightarrow>
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

inductive_cases hoare_elim_skip_cases [cases set]:
"\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> Skip sat [p, R, G, q,a]"



(* abbreviation 
 "stepc_rtrancl" :: "[('s,'p,'f) body,('s,'p,'f) config,('s,'p,'f) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sup>*/ _)" [81,81,81] 100)
 where                                
  "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sup>* cf1 \<equiv> ((CONST stepc \<Gamma>))\<^sup>*\<^sup>* cf0 cf1" *)


end
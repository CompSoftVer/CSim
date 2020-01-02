theory LocalRG_HoareDef                       
imports "SmallStepCon" "../EmbSimpl/HoarePartialDef" "../EmbSimpl/HoarePartialProps" 
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

type_synonym ('l,'g) state= "('l,'g) action_state"
type_synonym ('l,'g,'p,'f) rgformula =  
   "((('l,'g) state,'p,'f) com \<times>      (* c *)
    (('l,'g) state \<Rightarrow> bool) \<times>     (* P *)
    (('l,'g) state \<Rightarrow> bool) \<times>     (* I *)
    (('l,'g) transition \<Rightarrow> bool) \<times> (* R *)
    (('l,'g) transition \<Rightarrow> bool) \<times> (* G *)
    (('l,'g) state \<Rightarrow> bool) \<times> (* Q *)
    (('l,'g) state \<Rightarrow> bool))" (* A *)
    
type_synonym ('l,'g,'p,'f) septuple =  
   "('p \<times>      (* c *)
    (('l,'g) state \<Rightarrow> bool) \<times>     (* P *)
    (('l,'g) state \<Rightarrow> bool) \<times>     (* I *)
    (('l,'g) transition \<Rightarrow> bool) \<times> (* R *)
    (('l,'g) transition \<Rightarrow> bool) \<times> (* G *)
    (('l,'g) state \<Rightarrow> bool) \<times> (* Q *)
    (('l,'g) state \<Rightarrow> bool))" (* A *)    
    
definition env_tran::
    "('a \<Rightarrow> ('b::sep_algebra \<times> 'c::sep_algebra, 'a, 'd) LanguageCon.com option)
     \<Rightarrow> ('b \<times> 'c \<Rightarrow> bool)
        \<Rightarrow> (('b \<times> 'c, 'a, 'd) LanguageCon.com \<times> ('b \<times> 'c, 'd) xstate) list
           \<Rightarrow> (('b \<times> 'c) \<times> 'b \<times> 'c \<Rightarrow> bool) \<Rightarrow> bool"
where
"env_tran \<Gamma> q l rely \<equiv> snd(l!0) \<in> Normal ` (Collect q) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                  
                   (snd(l!i), snd(l!(Suc i))) \<in> 
                     (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (rely ** tran_Id) \<rfloor>))
"

definition env_tran_right::
    "('a \<Rightarrow> ('b::sep_algebra \<times> 'c::sep_algebra, 'a, 'd) LanguageCon.com option)     
        \<Rightarrow> (('b \<times> 'c, 'a, 'd) LanguageCon.com \<times> ('b \<times> 'c, 'd) xstate) list
           \<Rightarrow> (('b \<times> 'c) \<times> 'b \<times> 'c \<Rightarrow> bool) \<Rightarrow> bool"
where
"env_tran_right \<Gamma> l rely \<equiv> 
   (\<forall>i. Suc i<length l \<longrightarrow> 
        \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                  
        (snd(l!i), snd(l!(Suc i))) \<in> 
           (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (rely ** tran_Id) \<rfloor>))
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
  ultimately have "(snd ((l1@l2)! i), snd ((l1@l2) ! Suc i))
        \<in> (\<lambda>(x, y). (Normal x, Normal y)) ` (\<lfloor> (R \<and>* tran_Id) \<rfloor>)"
  using a0 unfolding env_tran_right_def by auto
  then have "(snd (l1! i), snd (l1 ! Suc i))
        \<in> (\<lambda>(x, y). (Normal x, Normal y)) ` (\<lfloor> (R \<and>* tran_Id) \<rfloor>)"
  using a1
  proof -
    have "\<forall>ps psa n. if n < length ps then (ps @ psa) ! n = (ps ! n::('b \<times> 'c, 'a, 'd) LanguageCon.com \<times> ('b \<times> 'c, 'd) xstate) else (ps @ psa) ! n = psa ! (n - length ps)"
      by (meson nth_append)
    then show ?thesis
      using \<open>(snd ((l1 @ l2) ! i), snd ((l1 @ l2) ! Suc i)) \<in> (\<lambda>(x, y). (Normal x, Normal y)) ` (\<lfloor> (R \<and>* tran_Id) \<rfloor>)\<close> \<open>Suc i < length l1\<close> by force
  qed 
  } then show "\<forall>i. Suc i < length l1 \<longrightarrow>
        \<Gamma>\<turnstile>\<^sub>c l1 ! i \<rightarrow>\<^sub>e l1 ! Suc i \<longrightarrow>
        (snd (l1 ! i), snd (l1 ! Suc i))
        \<in> (\<lambda>(x, y). (Normal x, Normal y)) ` (\<lfloor> (R \<and>* tran_Id) \<rfloor>)"
   by blast
qed
  

lemma env_tran_subl:"env_tran_right \<Gamma> (l1@l2) R \<Longrightarrow> env_tran_right \<Gamma> l2 R"
proof (induct "l1")
  case Nil thus ?case by auto
next
  case (Cons a l1) thus ?case by (fastforce intro:append_Cons env_tran_tail )
qed



lemma skip_fault_tran_false:
assumes a0:"(\<Gamma>,l) \<in> cptn" and
        a1:"Suc i<length l \<and> l!i=(Skip, t) \<and> (\<forall>t'. \<not>(t=Normal t'))" and
        a2: "env_tran_right \<Gamma> l rely" and
        a3: "\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>c\<^sub>e (l!(Suc i))"
shows "P"
proof -
  from a3 have "\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<or> \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i))"
  using step_ce_elim_cases by blast
  thus ?thesis
  proof
    assume "\<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow>\<^sub>e (l ! Suc i)"
    thus ?thesis using a2 a1 unfolding env_tran_right_def by auto
  next
    assume "\<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow> (l ! Suc i)"
    thus ?thesis using a1 by (metis (full_types) stepc_elim_cases(1)) 
  qed 
qed

lemma skip_fault_last:
assumes a0:"(\<Gamma>,l) \<in> cptn" and
        a1:"(i< (length l)) \<and> (l!i)=(Skip, t) \<and> (\<forall>t'. \<not>(t=Normal t'))" and
        a2: "env_tran_right \<Gamma> l rely" 
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
assumes a0:"env_tran_right \<Gamma> l rely" and
        a1:"Suc i < length l \<and>  \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))"
shows "\<exists>s1 s2. snd(l!i) = Normal s1 \<and> snd(l!(Suc i)) = Normal s2"
using a0 a1 unfolding env_tran_right_def by fastforce

lemma no_env_tran_not_normal:
assumes a0:"env_tran_right \<Gamma> l rely" and
        a1:"Suc i < length l \<and>  \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))" and
        a2:"(\<forall>s1. \<not> (snd(l!i) = Normal s1)) \<or> (\<forall>s2. \<not> (snd (l!Suc i) = Normal s2))"
shows "P"
using a0 a1 a2 unfolding env_tran_right_def by fastforce 
 
definition assum :: 
  "((('l::sep_algebra,'g::sep_algebra) state \<Rightarrow> bool) \<times>  
   (('l,'g) transition \<Rightarrow> bool) ) \<Rightarrow>
   'f set \<Rightarrow>
     ((('l,'g) state,'p,'f) confs) set" where
  "assum \<equiv> \<lambda>(pre, rely) F. 
             {c. snd((snd c)!0) \<in> Normal ` (Collect pre) \<and> (\<forall>i. Suc i<length (snd c) \<longrightarrow> 
                 (fst c)\<turnstile>\<^sub>c((snd c)!i)  \<rightarrow>\<^sub>e ((snd c)!(Suc i)) \<longrightarrow>                  
                   (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> 
                     (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (rely ** tran_Id) \<rfloor>))}"

                
lemma sub_assum:
  assumes a0: "(\<Gamma>,(x#l0)@l1) \<in> assum (p,R) F"
  shows "(\<Gamma>,x#l0) \<in> assum (p,R) F"    
proof -
  {have p0:"snd x \<in> Normal ` (Collect p)" 
    using a0 unfolding assum_def by force
  then have "env_tran_right \<Gamma> ((x#l0)@l1) R"
    using a0 unfolding assum_def 
    by (auto simp add: env_tran_right_def)
  then have env:"env_tran_right \<Gamma> (x#l0) R" 
    using env_tran_subr by blast 
  also have "snd ((x#l0)!0)  \<in> Normal ` (Collect p)" 
    using p0 by fastforce
  ultimately have "snd ((x#l0)!0)  \<in> Normal ` (Collect p) \<and> 
                  (\<forall>i. Suc i<length (x#l0) \<longrightarrow> 
                       \<Gamma>\<turnstile>\<^sub>c((x#l0)!i)  \<rightarrow>\<^sub>e ((x#l0)!(Suc i)) \<longrightarrow>                  
                       (snd((x#l0)!i), snd((x#l0)!(Suc i))) \<in> 
                         (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (R ** tran_Id) \<rfloor>))"
   unfolding env_tran_right_def by auto
  }    
  then show ?thesis  unfolding assum_def by auto
qed      

definition comm :: 
  "(('l::sep_algebra,'g::sep_algebra) transition \<Rightarrow> bool)  \<times> 
   ((('l,'g) state \<Rightarrow> bool)\<times> (('l,'g) state \<Rightarrow> bool)) \<Rightarrow>
   'f set \<Rightarrow> 
     ((('l,'g) state,'p,'f) confs) set" where
  "comm \<equiv> \<lambda>(guar, (q,a)) F. 
            {c. snd (last (snd c)) \<notin> Fault ` F  \<longrightarrow> 
                (\<forall>i ns ns'. 
                 Suc i<length (snd c) \<longrightarrow> 
                 (fst c)\<turnstile>\<^sub>c((snd c)!i)  \<rightarrow> ((snd c)!(Suc i)) \<longrightarrow>
                 snd ((snd c)!i) = Normal ns \<and> snd ((snd c)!(Suc i)) = Normal ns' \<longrightarrow>                               
                   (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> 
                      (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (guar ** tran_True) \<rfloor>)) \<and> 
                 (final (last (snd c))  \<longrightarrow>                   
                    ((fst (last (snd c)) = Skip \<and> 
                      snd (last (snd c)) \<in> Normal ` (Collect q))) \<or>
                    (fst (last (snd c)) = Throw \<and> 
                      snd (last (snd c)) \<in> Normal ` (Collect a)))}"

lemma comm_dest1:
"(\<Gamma>, l)\<in> comm (G,(q,a)) F \<Longrightarrow>
 Suc i<length l \<Longrightarrow>
 \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<Longrightarrow>
 snd (l!i) = Normal ns \<and> snd (l!(Suc i)) = Normal ns' \<Longrightarrow>
(snd(l!i), snd(l!(Suc i))) \<in> 
          (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>)"
unfolding comm_def
apply clarify
apply (erule allE)
by auto

lemma comm_dest2:
  assumes a0: "(\<Gamma>, l)\<in> comm (G,(q,a)) F" and
          a1: "final (last l)" and
          a2: "snd (last l) \<notin> Fault ` F" 
  shows  " ((fst (last l) = Skip \<and> 
            snd (last l) \<in> Normal ` (Collect q))) \<or>
            (fst (last l) = Throw \<and> 
            snd (last l) \<in> Normal ` (Collect a))"
proof -
  show ?thesis using a0 a1 a2 unfolding comm_def by auto
qed

definition com_validity :: 
  "(('l::sep_algebra,'g::sep_algebra) state,'p,'f) body \<Rightarrow> 
    'f set \<Rightarrow>
    (('l,'g) state,'p,'f) com \<Rightarrow> 
    (('l,'g) state \<Rightarrow> bool) \<Rightarrow> 
    (('l,'g) state \<Rightarrow> bool) \<Rightarrow>     
    (('l,'g) transition \<Rightarrow> bool) \<Rightarrow> 
    (('l,'g) transition \<Rightarrow> bool) \<Rightarrow>  
    (('l,'g) state \<Rightarrow> bool) \<Rightarrow> 
    (('l,'g) state \<Rightarrow> bool) \<Rightarrow> 
      bool" 
    ("_ \<Turnstile>\<^bsub>'/_\<^esub>/ _ sat [_,_, _, _, _,_]" [61,60,0,0,0,0,0,0,0] 45) where
  "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat [p, i , R, G, q,a] \<equiv> 
   \<forall>s. cp \<Gamma> Pr s \<inter> assum(p, R) F \<subseteq> comm(G, (q,a)) F"
   
definition com_cvalidity::
 "(('l::sep_algebra,'g::sep_algebra) state,'p,'f) body \<Rightarrow>
    ('l, 'g, 'p, 'f) septuple set \<Rightarrow>
    'f set \<Rightarrow>
    (('l,'g) state,'p,'f) com \<Rightarrow> 
    (('l,'g) state \<Rightarrow> bool) \<Rightarrow> 
    (('l,'g) state \<Rightarrow> bool) \<Rightarrow>     
    (('l,'g) transition \<Rightarrow> bool) \<Rightarrow> 
    (('l,'g) transition \<Rightarrow> bool) \<Rightarrow>  
    (('l,'g) state \<Rightarrow> bool) \<Rightarrow> 
    (('l,'g) state \<Rightarrow> bool) \<Rightarrow> 
      bool" 
    ("_,_ \<Turnstile>\<^bsub>'/_\<^esub>/ _ sat [_,_, _, _, _,_]" [61,60,0,0,0,0,0,0,0] 45) where
  "\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Pr sat [p, I , R, G, q,a] \<equiv> 
   (\<forall>(c,p,I,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, I , R, G, q,a]) \<longrightarrow> 
     \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat [p, I , R, G, q,a]"
     
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
     have concl:"(\<forall>i ns ns'. Suc i<length ?l \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c(?l!i)  \<rightarrow> (?l!(Suc i)) \<longrightarrow> 
               snd ((snd (\<Gamma>,?l))!i) = Normal ns \<and> snd ((snd (\<Gamma>,?l))!(Suc i)) = Normal ns' \<longrightarrow>
               snd ((snd (\<Gamma>,?l))!(Suc i)) \<notin> Fault ` F  \<longrightarrow>               
                 (snd(?l!i), snd(?l!(Suc i))) \<in> 
                   (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>))"
     proof -
       {fix i ns ns'
        assume a11:"Suc i < length  ?l" and
               a12:"\<Gamma>\<turnstile>\<^sub>c (?l ! i) \<rightarrow> ( ?l ! Suc i)" and
               a13:"snd ((snd (\<Gamma>,?l))!i) = Normal ns \<and> snd ((snd (\<Gamma>,?l))!(Suc i)) = Normal ns'"
        have p1:"(\<forall>i ns ns'. Suc i<length ?l1 \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c(?l1!i)  \<rightarrow> (?l1!(Suc i)) \<longrightarrow> 
               snd ((snd (\<Gamma>,?l1))!i) = Normal ns \<and> snd ((snd (\<Gamma>,?l1))!(Suc i)) = Normal ns' \<longrightarrow>
               snd ((snd (\<Gamma>,?l1))!(Suc i)) \<notin> Fault ` F  \<longrightarrow>               
               (snd(?l1!i), snd(?l1!(Suc i))) \<in> 
               (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>))"
        using a1 a3 unfolding comm_def by auto
        have "(snd (?l ! i), snd (?l ! Suc i))
        \<in> (\<lambda>(x, y). (Normal x, Normal y)) ` (\<lfloor> (G \<and>* tran_True) \<rfloor>)"         
        proof (cases i)
          case 0 
          have  "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow> (P, t)" using a12 a13 0 by auto
          thus ?thesis using a2 by auto             
        next
          case (Suc n) thus ?thesis
          proof -
            have f1: "\<Gamma>\<turnstile>\<^sub>c ((P, t) # xs) ! n \<rightarrow> ((P, t) # xs) ! Suc n"
              using Suc a12 by fastforce
            have f2: "Suc n < length ((P, t) # xs)"
              using Suc a11 by fastforce
            have f3: "snd (\<Gamma>, (P, t) # xs) = (P, t) # xs \<longrightarrow> snd (snd (\<Gamma>, (P, t) # xs) ! n) = Normal ns"
              using Suc a13 by auto
            have f4: "snd (\<Gamma>, (P, t) # xs) = (P, t) # xs \<longrightarrow> snd (snd (\<Gamma>, (P, t) # xs) ! Suc n) = Normal ns'"
              using Suc a13 by auto
            have "snd (snd (\<Gamma>, (P, t) # xs) ! Suc n) \<notin> Fault ` F \<and> snd (\<Gamma>, (P, t) # xs) = (P, t) # xs"
              using Suc a13 by force
            hence "(snd (((P, t) # xs) ! n), snd (((P, t) # xs) ! Suc n)) \<in> (\<lambda>(pa, p). (Normal pa, Normal p)) ` (\<lfloor> (G \<and>* tran_True) \<rfloor>)"
              using f4 f3 f2 f1 p1 by blast
            thus ?thesis
              by (simp add: Suc)
          qed  
        qed
       } thus ?thesis by auto
     qed
     have concr:"(final (last ?l)  \<longrightarrow> 
                  snd (last ?l) \<notin> Fault ` F  \<longrightarrow>
                    ((fst (last ?l) = Skip \<and> 
                      snd (last ?l) \<in> Normal ` (Collect q))) \<or>
                    (fst (last ?l) = Throw \<and> 
                      snd (last ?l) \<in> Normal ` (Collect a)))"
     using a1 unfolding comm_def by auto
     note res=conjI[OF concl concr]}
     thus ?thesis unfolding comm_def by auto qed   
qed

lemma ctran_in_comm:   
  " (G \<and>* tran_True)  (s,s)  \<Longrightarrow>
   (\<Gamma>,(Q, Normal s) # xs) \<in> comm(G, (q,a)) F  \<Longrightarrow>        
   (\<Gamma>,(P, Normal s) # (Q, Normal s) # xs) \<in> comm(G, (q,a)) F"
proof -
  assume a1:"(G \<and>* tran_True)  (s,s)" and
         a2:"(\<Gamma>,(Q, Normal s) # xs) \<in> comm(G, (q,a)) F"          
  show ?thesis using comm_def a1 a2
  proof -
     {
     let ?l1 = "(Q, Normal s) # xs"
     let ?l = "(P, Normal s) # ?l1"
     have concl:"(\<forall>i ns ns'. Suc i<length ?l \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c(?l!i)  \<rightarrow> (?l!(Suc i)) \<longrightarrow> 
               snd ((snd (\<Gamma>,?l))!i) = Normal ns \<and> snd ((snd (\<Gamma>,?l))!(Suc i)) = Normal ns' \<longrightarrow>
               snd ((snd (\<Gamma>,?l))!(Suc i)) \<notin> Fault ` F  \<longrightarrow>               
                 (snd(?l!i), snd(?l!(Suc i))) \<in> 
                   (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>))"
     proof -
       {fix i ns ns'
        assume a11:"Suc i < length  ?l" and
               a12:"\<Gamma>\<turnstile>\<^sub>c (?l ! i) \<rightarrow> ( ?l ! Suc i)" and
               a13:"snd ((snd (\<Gamma>,?l))!i) = Normal ns \<and> snd ((snd (\<Gamma>,?l))!(Suc i)) = Normal ns'"
        have p1:"(\<forall>i ns ns'. Suc i<length ?l1 \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c(?l1!i)  \<rightarrow> (?l1!(Suc i)) \<longrightarrow> 
               snd ((snd (\<Gamma>,?l1))!i) = Normal ns \<and> snd ((snd (\<Gamma>,?l1))!(Suc i)) = Normal ns' \<longrightarrow>
               snd ((snd (\<Gamma>,?l1))!(Suc i)) \<notin> Fault ` F  \<longrightarrow>               
               (snd(?l1!i), snd(?l1!(Suc i))) \<in> 
               (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>))"
        using a2 unfolding comm_def by auto
        have "(snd (?l ! i), snd (?l ! Suc i))
        \<in> (\<lambda>(x, y). (Normal x, Normal y)) ` (\<lfloor> (G \<and>* tran_True) \<rfloor>)"   
        proof (cases i)
          case 0     
          then have "snd (((P, Normal s) # (Q, Normal s) # xs) ! i) = Normal s \<and> 
                     snd (((P, Normal s) # (Q, Normal s) # xs) ! (Suc i)) = Normal s"                
            by fastforce

          also have "(s, s) \<in> \<lfloor> (G \<and>* tran_True) \<rfloor>"
             using Satis_def a1 by blast
          then have "(Normal s, Normal s)\<in> (\<lambda>(x, y). (Normal x, Normal y)) `
                     (\<lfloor> (G \<and>* tran_True) \<rfloor>)"
             by fastforce
          ultimately show  ?thesis using a1 Satis_def by auto            
        next
          case (Suc n) thus ?thesis using p1 a2  a11 a12 a13
          proof -
            have f1: "\<Gamma>\<turnstile>\<^sub>c ((Q, Normal s) # xs) ! n \<rightarrow> ((Q, Normal s) # xs) ! Suc n"
              using Suc a12 by fastforce
            have f2: "Suc n < length ((Q, Normal s) # xs)"
              using Suc a11 by fastforce
            have f3: "snd (\<Gamma>, (Q, Normal s) # xs) = (Q, Normal s) # xs \<longrightarrow> snd (snd (\<Gamma>, (Q, Normal s) # xs) ! n) = Normal ns"
              using Suc a13 by auto
            have f4: "snd (\<Gamma>, (Q, Normal s) # xs) = (Q, Normal s) # xs \<longrightarrow> snd (snd (\<Gamma>, (P, Normal s) # xs) ! Suc n) = Normal ns'"
              using Suc a13 by auto
            have "snd (snd (\<Gamma>, (Q, Normal s) # xs) ! Suc n) \<notin> Fault ` F \<and> snd (\<Gamma>, (Q, Normal s) # xs) = (Q, Normal s) # xs"
              using Suc a13 by force
            hence "(snd (((Q, Normal s) # xs) ! n), snd (((Q, Normal s) # xs) ! Suc n)) \<in> (\<lambda>(pa, p). (Normal pa, Normal p)) ` (\<lfloor> (G \<and>* tran_True) \<rfloor>)"
              using f4 f3 f2 f1 p1 by (metis nth_Cons_Suc snd_conv) 
            thus ?thesis
              by (simp add: Suc)
          qed  
        qed
       } thus ?thesis by auto
     qed
     have concr:"(final (last ?l)  \<longrightarrow> 
                  snd (last ?l) \<notin> Fault ` F  \<longrightarrow>
                    ((fst (last ?l) = Skip \<and> 
                      snd (last ?l) \<in> Normal ` (Collect q))) \<or>
                    (fst (last ?l) = Throw \<and> 
                      snd (last ?l) \<in> Normal ` (Collect a)))"
     using a2 unfolding comm_def by auto
     note res=conjI[OF concl concr]}
     thus ?thesis unfolding comm_def by auto qed
qed


text{* 
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
                     (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (R ** tran_Id) \<rfloor>))) \<and>      
        (h1 \<uplus>\<^sub>p h2) h \<longrightarrow>
        (\<forall>c\<in> cp \<Gamma> f (Normal h). 
          final_valid(last (snd c)) \<and>
          (\<forall>i. Suc i<length (snd c) \<longrightarrow> 
              (fst c)\<turnstile>\<^sub>c((snd c)!i)  \<rightarrow>\<^sub>e ((snd c)!(Suc i)) \<longrightarrow>                  
              (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> 
                (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (R ** tran_Id) \<rfloor>)) \<longrightarrow>
              (Normal (t1 \<uplus> h2) =  snd (last (snd c)))))     
      "                         
 
 lemma valid_safe_RG_safe_valid: 
    "\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Pr sat [p, I , R, G, q,a] \<and>
     (rel_safe (R\<and>*tran_Id))\<and> (rel_safe (G\<and>*tran_True)) \<Longrightarrow> mem_safe \<Gamma> Pr R"
     
  sorry
     
subsection \<open>Validity for Parallel Programs.\<close>
definition All_End :: "('s,'p,'f) par_config \<Rightarrow> bool" where
  "All_End xs \<equiv> \<forall>c\<in>set (fst xs). final_valid (c,snd xs)"

definition par_assum :: 
  "((('l::sep_algebra,'g::sep_algebra) state \<Rightarrow> bool) \<times>  
   (('l,'g) transition \<Rightarrow> bool) ) \<Rightarrow>
   'f set \<Rightarrow>
     ((('l,'g) state,'p,'f) par_confs) set" where
  "par_assum \<equiv> 
     \<lambda>(pre, rely) F. {c. 
       snd((snd c)!0) \<in> Normal ` (Collect pre) \<and> (\<forall>i. Suc i<length (snd c) \<longrightarrow> 
       (fst c)\<turnstile>\<^sub>p((snd c)!i)  \<rightarrow>\<^sub>e ((snd c)!(Suc i)) \<longrightarrow>        
         (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> 
           (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (rely ** tran_Id) \<rfloor>))}"
           
definition par_comm :: 
  "(('l::sep_algebra,'g::sep_algebra) transition \<Rightarrow> bool)  \<times> 
     ((('l,'g) state \<Rightarrow> bool)\<times> (('l,'g) state \<Rightarrow> bool))  \<Rightarrow> 
    'f set \<Rightarrow>
   ((('l,'g) state,'p,'f) par_confs) set" where
  "par_comm \<equiv> 
     \<lambda>(guar, (q,a)) F. {c. 
       (\<forall>i ns ns'. Suc i<length (snd c) \<longrightarrow> 
           (fst c)\<turnstile>\<^sub>p((snd c)!i)  \<rightarrow> ((snd c)!(Suc i)) \<longrightarrow> 
           snd ((snd c)!i) = Normal ns \<and> snd ((snd c)!(Suc i)) = Normal ns' \<longrightarrow> 
           snd ((snd c)!(Suc i)) \<notin> Fault ` F  \<longrightarrow>
           (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> 
             (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (guar ** tran_True) \<rfloor>)) \<and> 
           (All_End (last (snd c)) \<longrightarrow> (\<exists>j. fst (last (snd c))!j=Throw \<and> 
                                              snd (last (snd c)) \<in> Normal ` (Collect a)) \<or>
                                       (\<forall>j. fst (last (snd c))!j=Skip \<and>
                                              snd (last (snd c)) \<in> Normal ` (Collect q)))}"

definition par_com_validity :: 
  "(('l::sep_algebra,'g::sep_algebra) state,'p,'f) body \<Rightarrow> 
   'f set \<Rightarrow>
   (('l,'g) state,'p,'f) par_com \<Rightarrow> 
   (('l,'g) state \<Rightarrow> bool) \<Rightarrow> 
   (('l,'g) state \<Rightarrow> bool) \<Rightarrow> 
   (('l,'g) transition \<Rightarrow> bool) \<Rightarrow> 
   (('l,'g) transition \<Rightarrow> bool) \<Rightarrow> 
   (('l,'g) state \<Rightarrow> bool) \<Rightarrow>
   (('l,'g) state \<Rightarrow> bool) \<Rightarrow> 
     bool"  
("_ \<Turnstile>\<^bsub>'/_\<^esub>/ _ SAT [_, _,_, _, _,_]" [61,60,0,0,0,0,0,0,0] 45) where
  "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Ps SAT [pre, i,R, G, q,a] \<equiv> 
   \<forall>s. par_cp \<Gamma> Ps s \<inter> par_assum(pre, R) F \<subseteq> par_comm(G, (q,a)) F"
   
definition par_com_cvalidity :: 
  "(('l::sep_algebra,'g::sep_algebra) state,'p,'f) body \<Rightarrow>
    ('l,'g,'p,'f) septuple set \<Rightarrow>
   'f set \<Rightarrow>
   (('l,'g) state,'p,'f) par_com \<Rightarrow> 
   (('l,'g) state \<Rightarrow> bool) \<Rightarrow> 
   (('l,'g) state \<Rightarrow> bool) \<Rightarrow> 
   (('l,'g) transition \<Rightarrow> bool) \<Rightarrow> 
   (('l,'g) transition \<Rightarrow> bool) \<Rightarrow> 
   (('l,'g) state \<Rightarrow> bool) \<Rightarrow>
   (('l,'g) state \<Rightarrow> bool) \<Rightarrow> 
     bool"  
("_,_ \<Turnstile>\<^bsub>'/_\<^esub>/ _ SAT [_, _,_, _, _,_]" [61,60,0,0,0,0,0,0,0] 45) where
  "\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Ps SAT [p, I, R, G, q,a] \<equiv> 
  (\<forall>(c,p,I,R,G,q,a)\<in> \<Theta>. (\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, I , R, G, q,a])) \<longrightarrow>
   \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Ps SAT [p, I , R, G, q,a]"
   
declare Un_subset_iff [simp del] sup.bounded_iff [simp del]

inductive
lrghoare :: "[(('l::cancellative_sep_algebra,'g::cancellative_sep_algebra) state,'p,'f) body,
             ('l,'g,'p,'f) septuple set,
              'f set,
              (('l,'g) state,'p,'f) com,  
              (('l,'g) state \<Rightarrow> bool), 
              (('l,'g) state \<Rightarrow> bool), 
              (('l,'g) transition \<Rightarrow> bool), (('l,'g) transition \<Rightarrow> bool),
              (('l,'g) state \<Rightarrow> bool),
               (('l,'g) state \<Rightarrow> bool)] \<Rightarrow> bool"
    ("_,_ \<turnstile>\<^bsub>'/_\<^esub> _ sat [_, _, _, _, _,_]" [61,61,60,60,0,0,0,0,0] 45)
where
 Skip: "\<lbrakk> Sta q (R\<and>*tran_Id);           
          \<forall>s t. ((q or (q or a)) imp (I\<and>*sep_true)) (s,t);
          I  \<triangleright> R; I  \<triangleright> G\<rbrakk> \<Longrightarrow>
         \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> Skip sat [q, I, R, G, q,a] "

|Spec: "\<lbrakk>Collect p \<subseteq> {s. (\<forall>t. (s,t)\<in>r \<longrightarrow> t \<in> Collect q) \<and> (\<exists>t. (s,t) \<in> r)};
        \<forall>s t. ((p or (q or a)) imp (I\<and>*sep_true)) (s,t);
        \<forall>s t. ((p \<unrhd> q) imp (G\<and>*tran_True)) (s,t);
        Sta p (R\<and>*tran_Id);Sta q (R\<and>*tran_Id);
        I  \<triangleright> R; I  \<triangleright> G\<rbrakk> \<Longrightarrow> \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Spec r) sat [p, I, R, G, q,a]"

| Basic: "\<lbrakk> Collect p \<subseteq> {s. f s \<in> (Collect q)}; 
           \<forall>s t. ((p or (q or a)) imp (I\<and>*sep_true)) (s,t);
           \<forall>s t. ((p \<unrhd> q) imp (G\<and>*tran_True)) (s,t);
           Sta p (R\<and>*tran_Id); Sta q (R\<and>*tran_Id); I  \<triangleright> R; I  \<triangleright> G \<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Basic f) sat [p, I, R, G, q,a]"

| If: "\<lbrakk> \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p and (set_fun b), I, R, G, q,a]; 
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [p and (not (set_fun b)), I, R, G, q,a]; 
        \<forall>s t. (p imp I) (s,t);
        Sta p (R\<and>*tran_Id)
        \<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Cond b c1 c2) sat [p, I, R, G, q,a]"

| While: "\<lbrakk> \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p and (set_fun b), I, R, G, p,a];
            \<forall>s t. (p imp I) (s,t)\<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (While b c) sat [p, I, R, G, p and (not (set_fun b)),a]"

| Seq: "\<lbrakk> \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p, I, R, G, q,a]; \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [q, I, R, G, r,a]\<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Seq c1 c2) sat [p, I, R, G, r,a]"

| Await: "\<lbrakk> \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> (Collect p \<inter> b) c (Collect q),(Collect a);
           \<forall>s t. ((p or (q or a)) imp (I\<and>*sep_true)) (s,t);
           \<forall>s t. ((p \<unrhd> (q or a)) imp (G\<and>*tran_True)) (s,t);
           Sta p (R\<and>*tran_Id); Sta q (R\<and>*tran_Id); Sta a (R\<and>*tran_Id); I  \<triangleright> R; I  \<triangleright> G \<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Await b c) sat [p, I, R, G, q,a]"

| Guard: "\<lbrakk> \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p and (set_fun g), I, R, G, q,a] \<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Guard f g c) sat [p and (set_fun g), I, R, G, q,a]"

| Guarantee:  "\<lbrakk> f\<in>F; \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p and (set_fun g), I, R, G, q,a];
               (\<forall>s t. (p and (not ((\<lambda>s. s\<in>g))) imp (I\<and>*sep_true)) (s,t));
                Sta (p and (not (set_fun g))) (R\<and>*tran_Id) \<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Guard f g c) sat [p, I, R, G, q,a]"

| CallRec: "\<lbrakk>(c,p,I,R,G,q,a) \<in> Specs; 
             \<forall>(c,p,I,R,G,q,a)\<in> Specs. c \<in> dom \<Gamma> \<and> 
             \<Gamma>,\<Theta> \<union> Specs \<turnstile>\<^bsub>/F\<^esub> (the (\<Gamma> c)) sat [p, I, R, G, q,a]\<rbrakk> \<Longrightarrow>
            \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, I, R, G, q,a]"

| Asm: "\<lbrakk>(c,p,I,R,G,q,a) \<in> \<Theta>;\<forall>s t. ((p or (q or a)) imp (I\<and>*sep_true)) (s,t);
         I  \<triangleright> R; I  \<triangleright> G;
        Sta p (R\<and>*tran_Id) \<and> Sta q (R\<and>*tran_Id) \<and> Sta a (R\<and>*tran_Id)\<rbrakk> 
        \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, I, R, G, q,a]"

| Call: "\<lbrakk>c \<in> dom \<Gamma>; 
         \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (the (\<Gamma> c)) sat [p, I, R, G, q,a];
         \<forall>s t. (p imp I) (s,t);
         Sta p (R\<and>*tran_Id)\<rbrakk> 
        \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, I, R, G, q,a]"

| DynCom: "(\<forall>s \<in> Collect p. (\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (c s) sat [p, I, R, G, q,a])) \<Longrightarrow>
           (\<forall>s t. ((p or (q or a)) imp (I\<and>*sep_true)) (s,t)) \<and>
           (I  \<triangleright> R) \<and> (I  \<triangleright> G) \<Longrightarrow>
          (Sta p (R\<and>*tran_Id)) \<and> (Sta q (R\<and>*tran_Id)) \<and> (Sta a (R\<and>*tran_Id)) \<Longrightarrow>
            \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (DynCom c) sat [p, I, R, G, q,a]"

| Throw: "\<lbrakk> 
          Sta a (R\<and>*tran_Id); 
           \<forall>s t. ((p or (q or a)) imp (I\<and>*sep_true)) (s,t);
          I  \<triangleright> R; I  \<triangleright> G\<rbrakk> \<Longrightarrow>
         \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> Throw sat [a, I, R, G, q,a] "

| Catch: "\<lbrakk> \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p, I, R, G, q,r]; \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [r, I, R, G, r,a]\<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Catch c1 c2) sat [p, I, R, G, r,a]"


| Conseq: "\<forall>s \<in> (Collect p). 
             (\<exists>p' R' G' q' a' I'.  (p' s) \<and>
             (\<forall>s t. (R  imp R') (s,t)) \<and>            
             (\<forall>s t. (G' imp G) (s,t)) \<and>             
             (\<forall>s. (q' imp q) s) \<and>
             (\<forall>s. (a' imp a) s) \<and>
             (\<forall>s t. ((p' or (q' or a')) imp (I'\<and>*sep_true)) (s,t)) \<and>             
            (I'  \<triangleright> R')\<and> (I' \<triangleright> G') \<and>             
            (\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p', I', R', G', q',a']) ) \<Longrightarrow>
           (\<forall>s t. ((p or (q or a)) imp (I\<and>*sep_true)) (s,t)) \<and>
          (I  \<triangleright> R) \<and> (I  \<triangleright> G) 
            \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, I, R, G, q,a]"

| Env:  "\<lbrakk>noawaits c; \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> (Collect p ) (sequential c) (Collect q),(Collect a)\<rbrakk> \<Longrightarrow>
         \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> c sat [p, sep_empty, Emp, Emp, q,a]"
        
| Hide: "\<lbrakk>\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p, (I \<and>* I'), (R \<and>* R'), (G \<and>* G'), q,a]; 
         (I  \<triangleright> R); 
         (I  \<triangleright> G)
          \<rbrakk> \<Longrightarrow> 
         \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> c sat [p, I, R, G, q,a]" 

|Frame: "\<lbrakk>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [(p::('l::cancellative_sep_algebra,'g::cancellative_sep_algebra) state \<Rightarrow> bool), I, R, G , q,a]; 
        I'  \<triangleright> R'; I'  \<triangleright> G';
        Sta r (R'\<and>*tran_Id);
        (\<forall>s t. (r imp (I'\<and>*sep_true))(s,t));
        (rel_safe (R\<and>*tran_Id)); (rel_safe (G\<and>*tran_True)) \<rbrakk>  \<Longrightarrow>
        \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> c sat [p\<and>*r, I \<and>* I', R \<and>* R', G \<and>* G', q\<and>*r,a\<and>*r]"

definition Pre :: " ('l,'g,'p,'f)rgformula \<Rightarrow> (('l,'g) state \<Rightarrow> bool)" where
  "Pre x \<equiv> fst(snd(snd x))"

definition Post :: "('l,'g,'p,'f) rgformula \<Rightarrow> (('l,'g) state \<Rightarrow> bool)" where
  "Post x \<equiv>  fst(snd(snd(snd(snd(snd x)))))"

definition Inva :: "('l,'g,'p,'f) rgformula \<Rightarrow> (('l,'g) state \<Rightarrow> bool)" where
  "Inva x \<equiv> fst(snd(snd x))"

definition Abr :: "('l,'g,'p,'f) rgformula \<Rightarrow> (('l,'g) state \<Rightarrow> bool)" where
  "Abr x \<equiv> fst(snd(snd(snd(snd(snd x)))))"

definition Rely :: "('l,'g,'p,'f) rgformula \<Rightarrow> (('l,'g) transition \<Rightarrow> bool)" where
  "Rely x \<equiv> fst(snd(snd(snd x)))"

definition Guar :: "('l,'g,'p,'f) rgformula \<Rightarrow> (('l,'g) transition \<Rightarrow> bool)" where
  "Guar x \<equiv> fst(snd(snd(snd(snd x))))"

definition Com :: "('l,'g,'p,'f) rgformula \<Rightarrow> (('l,'g) state,'p,'f) com" where
  "Com x \<equiv> fst  x"


inductive
  par_rghoare ::  "[(('l::cancellative_sep_algebra,'g::cancellative_sep_algebra) state,'p,'f) body,
              ('l,'g,'p,'f) septuple set,
              'f set,
              ( ('l,'g,'p,'f) rgformula) list,  
              (('l,'g) state \<Rightarrow> bool), 
              (('l,'g) state \<Rightarrow> bool), 
              (('l,'g) transition \<Rightarrow> bool), (('l,'g) transition \<Rightarrow> bool),
              (('l,'g) state \<Rightarrow> bool),
               (('l,'g) state \<Rightarrow> bool)] \<Rightarrow> bool"
    ("_,_ \<turnstile>\<^bsub>'/_\<^esub> _ SAT [_, _, _, _, _,_]" [61,60,60,0,0,0,0,0] 45)
where
  Parallel:
  "\<lbrakk> \<forall>i<length xs. (Collect R) \<union> (\<Union>j\<in>{j. j<length xs \<and> j\<noteq>i}. (Collect (Guar(xs!j)))) \<subseteq> (Collect (Rely(xs!i)));
    (\<Union>j<length xs. (Collect (Guar(xs!j)))) \<subseteq> (Collect G);
     (Collect pre) \<subseteq> (\<Inter>i<length xs. (Collect (Pre(xs!i))));
    (\<Inter>i<length xs. (Collect (Post(xs!i)))) \<subseteq> (Collect post);
    (\<Union>i<length xs. (Collect (Abr(xs!i)))) \<subseteq> (Collect abr);
    (p = (pr \<and>* r)) \<and> (\<forall>i<length xs. \<exists>pi. Pre(xs!i) = (pi \<and>* r));
    (q = (qr\<and>*rq)) \<and> (\<forall>i<length xs.(\<Inter>{crj.  \<exists>rj qj. Post(xs!i) = (qj\<and>*rj) \<and> crj=Collect rj} \<subseteq> Collect rq));
    (a = (ab\<and>*rabr)) \<and> (\<forall>i<length xs.(\<Union>{crj.  \<exists>abrj rabrj. Abr(xs!i) = (abrj\<and>*rabrj) \<and> crj=Collect rj} \<subseteq> Collect rabr));
     \<forall>s t.((r or rq or rabr) imp I)(s,t);
    (* ((Collect r) \<union> (\<Union>{crj. \<forall>i<length xs. \<exists>abrj rabrj. Abr(xs!i) = (abrj\<and>*rabrj) \<and> crj= Collect rj} )) \<subseteq> (Collect inva); *)
    I  \<triangleright> R;
    \<forall>i<length xs. \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> Com(xs!i) sat [Pre(xs!i),Inva(xs!i),Rely(xs!i),Guar(xs!i),Post(xs!i),Abr(xs!i)] \<rbrakk>
   \<Longrightarrow>  \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> xs SAT [p, I, R, G, q,a]"

section {* Soundness *}
lemma satis_wellformed:
  assumes a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p, I, R, G, q,a]"                   
  shows "((I \<triangleright> R) \<and> 
         (I  \<triangleright> G) \<and> 
         (\<forall>s t. ((p or (q or a)) imp (I\<and>*sep_true)) (s,t)))"
using a0
proof(induct  rule:lrghoare.induct)
  case Skip thus ?case by auto
next
  case (Spec) thus ?case by auto
next
  case (Basic) thus ?case by auto
next
  case (If \<Gamma> \<Theta> F c1 p b I R G q a c2) thus ?case by blast  
next
  case (While \<Gamma> \<Theta> F c p b I R G a)
   thus ?case by auto
next
  case (Seq) thus ?case by auto
next
  case (Await) thus ?case by auto
next
  case (Guard) thus ?case by auto
next
  case (Guarantee) thus ?case by auto
next
  case (CallRec) thus ?case by auto
next
  case (DynCom p \<Gamma> \<Theta> F c I R G q a) thus ?case by auto    
next
  case (Throw) thus ?case by auto
next
  case (Catch) thus ?case by auto
next
  case (Asm) thus ?case by auto
next
  case (Conseq) thus ?case  by auto
next
  case (Env) thus ?case 
  by (auto simp add: Fence_def satis_emp Emp_def after_def precise_empty)  
next
  case (Hide) thus ?case by (metis sep_conj_assoc sep_conj_sep_true_right)
next
  case (Frame \<Gamma> \<Theta> F c p I R G q a I' R' G' r) 
  then have "((I \<and>* I') \<triangleright> (R \<and>* R')) \<and> ((I \<and>* I') \<triangleright> (G \<and>* G'))" 
    using fence4 by auto 
  also have "(\<forall>s t. (p \<and>* r) (s, t) \<or> (q \<and>* r) (s, t) \<or> (a \<and>* r) (s, t) \<longrightarrow>
           ((I \<and>* I') \<and>* sep_true) (s, t))"       
       proof -
         have "\<forall>p. ((I \<and>* (\<lambda>p. True)) \<and>* I' \<and>* (\<lambda>p. True)) p \<and> ((I \<and>* I') \<and>* (\<lambda>p. True)) p \<or> \<not> ((I \<and>* I') \<and>* (\<lambda>p. True)) p \<and> \<not> ((I \<and>* (\<lambda>p. True)) \<and>* I' \<and>* (\<lambda>p. True)) p"
           by (simp add: sep_conj_left_commute star_op_comm)
        then have "\<forall>t.((I \<and>* sep_true) \<and>* (I' \<and>* sep_true)) t = ((I \<and>* I') \<and>* sep_true) t"
          by blast          
        then have "(\<forall>s t. ((p or (q or a)) \<and>* r) (s,t) \<longrightarrow> 
                      ((I \<and>* I') \<and>* sep_true) (s,t))"
           using Frame(2) Frame(6) or_sep[of "(p or (q or a))" "(I \<and>* (\<lambda>s. True))" "r" "(I' \<and>* (\<lambda>s. True))"] 
           by auto
        also have " (\<forall>s t. ((p or (q or a)) \<and>* r) (s,t) = ((p \<and>* r)or ((q\<and>* r) or (a\<and>* r))) (s,t))"
          by (simp add: sep_conj_disj)         
        ultimately show ?thesis by auto         
       qed
   ultimately show ?case by auto                       
qed

(*

lemma 
  assumes a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p, I, R, G, q,a]"                   
  shows "Sta p (R\<and>*tran_Id)"
using a0
proof(induct  rule:lrghoare.induct)
  case Skip thus ?case by auto
next
  case (Spec) thus ?case by auto
next
  case (Basic) thus ?case by auto
next
  case (If \<Gamma> \<Theta> F c1 p b I R G q a c2) thus ?case 
   unfolding Sta_def by blast

next
  case (While \<Gamma> \<Theta> F c p b I R G a) thus ?case 
   unfolding Sta_def by blast 
next
  case (Seq) thus ?case by auto
next
  case (Await) thus ?case by auto
next
  case (Guard) thus ?case by auto
next
  case (Guarantee) thus ?case unfolding Sta_def by blast 
next
  case (CallRec) thus ?case by auto
next
  case (DynCom p \<Gamma> \<Theta> F c I R G q a) thus ?case by auto    
next
  case (Throw) thus ?case by auto
next
  case (Catch) thus ?case by auto
next
  case (Asm) thus ?case by auto
next
  case (Conseq) thus ?case  by auto
next
  case (Env) thus ?case by (metis Sta_def empty_neutral sep_conj_commute tran_Id_eq)     
next
  case (Hide) thus ?case by auto
next
  (* proof sep_true \<triangleright> tran_Id by def of tran_id and I \<triangleright> I x I *)
  case (Frame \<Gamma> \<Theta> F c p I R G q a I' R' G' r) 
  then have "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> c sat [p\<and>*r, I \<and>* I', R \<and>* R', G \<and>* G', q\<and>*r,a\<and>*r]" using lrghoare.Frame by blast
  then have a1:"((I \<and>* I')  \<triangleright>  (R \<and>* R')) \<and> ((\<forall>s t. (p\<and>*r) (s, t) \<longrightarrow> ((I \<and>* I') \<and>* sep_true) (s, t)))"
  using satis_wellformed sep_conj_disj by blast
  then have imp:"(I \<triangleright> R) \<and> (\<forall>s t. p (s, t) \<longrightarrow> (I \<and>* sep_true) (s, t))"
  using satis_wellformed sep_conj_disj Frame by blast  
  then have "(I \<and>* (\<lambda>s. True)) \<triangleright> R \<and>* tran_Id" using a1 Frame unfolding tran_Id_def sorry
  then have "Sta (p \<and>* r) ((R \<and>* tran_Id) \<and>* (R'\<and>* tran_Id))" 
  using Frame(2) Frame(5) imp sta_fence[of p "R \<and>* tran_Id" r "R' \<and>* tran_Id" "I \<and>* sep_true"]
   by auto
  also have "(tran_Id \<and>* tran_Id) = tran_Id" unfolding tran_Id_def satis_def using sep_conj_true sorry
  ultimately show ?case 
    proof -
      have "Sta (p \<and>* r) (R \<and>* tran_Id \<and>* R')"
        by (metis (no_types) `(tran_Id \<and>* tran_Id) = tran_Id` `Sta (p \<and>* r) ((R \<and>* tran_Id) \<and>* R' \<and>* tran_Id)` sep_conj_assoc sep_conj_commute)
      thus ?thesis
        by (metis (no_types) sep_conj_assoc sep_conj_commute)
    qed 
qed

*)

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
  assumes a3:"env_tran_right \<Gamma> l rely"
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
      assumes a4:"env_tran_right \<Gamma> l rely" 
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
         a4: "env_tran_right \<Gamma> l rely"    
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
         a3: "\<forall>j. j\<ge>i \<and> Suc j < length l \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"  and
         a4: "env_tran_right \<Gamma> l rely"              
   shows "P" 
using a0 a1 a2 a3 a4  only_one_component_tran_j
by blast


lemma zero_skip_all_skip: 
      assumes a1:"(\<Gamma>, l) \<in> cptn \<and> fst (l!0) = Skip \<and>  i < length l"
      shows "fst (l!i) = Skip"
using a1 i_skip_all_skip by blast

lemma zero_throw_all_throw:
      assumes a1:"(\<Gamma>, l) \<in> cptn \<and> fst (l!0) = Throw \<and> snd(l!0) = Normal s1 \<and>  i < length l"
      assumes a2: "env_tran_right \<Gamma> l rely" 
      shows "fst (l!i) = Throw \<and> (\<exists>s2. snd (l!i) = Normal s2)"
using a1 a2 i_throw_all_throw by blast

lemma only_one_component_tran_0:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "(fst (l!0) = Skip) \<or> (fst (l!0) = Throw \<and> snd(l!0) = Normal s1)" and                  
         a2: "Suc j < length l" and
         a3: "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"  and
         a4: "env_tran_right \<Gamma> l rely"         
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
         a4: "env_tran_right \<Gamma> l rely"      
   shows "P" 
using a0 a1 a2 a3 a4
proof (induct i)
  case 0 thus ?thesis using only_one_component_tran_0 0 by blast
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
              a4: "env_tran_right \<Gamma> l rely"
      shows "\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))"
proof -
   have "\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>c\<^sub>e (l!(Suc i))" using a1 a2 a3 cptn_tran_ce_i by auto   
   also have "\<not> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" using a1 a2 a3 a4 using only_one_component_tran_0 by blast             
   ultimately show ?thesis by (simp add: step_ce.simps) 
qed

lemma final_always_env_i: 
      assumes a1:"(\<Gamma>, l) \<in> cptn" and
              a2: "fst (l!i) = Skip \<or> (fst (l!i) = Throw \<and> snd(l!i) = Normal s1)" and
              a3: "j\<ge>i \<and> Suc j<length l" and
              a4: "env_tran_right \<Gamma> l rely"
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
  assumes a0:"Sta q (R \<and>* tran_Id)"  and       
          a1: "snd(l!i) \<in> Normal ` (Collect q)" and
          a2:"(snd(l!i), snd(l!(Suc i))) \<in> 
             (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (R \<and>* tran_Id) \<rfloor>)"
  shows "snd(l!(Suc i)) \<in> Normal ` (Collect q)"
using a0  a1  a2 
unfolding Sta_def Satis_def  by auto 

lemma stability:
assumes   a0:"Sta q (R \<and>* tran_Id)"  and                 
          a1: "snd(l!j) \<in> Normal ` (Collect q)" and
          a2: "j\<le>k \<and> k < (length l)" and
          a3: "n=k-j" and
          a4: "\<forall>i. j\<le>i \<and> i < k \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))" and
          a5:"env_tran_right \<Gamma> l R"
      shows "snd (l!k) \<in> Normal ` (Collect q) \<and> fst (l!j) = fst (l!k)"
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
    ultimately have induct:"snd (l! (k-1)) \<in> Normal ` (Collect q) \<and> fst (l!j) = fst (l!(k-1))" using Suc
      by blast      
    also have j_1:"k-1+1=k" using Cons Suc.prems(4) by auto 
    have f1:"\<forall>i. j\<le>i \<and> i < k \<longrightarrow> (snd((snd (\<Gamma>,l))!i), snd((snd (\<Gamma>,l))!(Suc i))) \<in> 
                     (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (R \<and>* tran_Id) \<rfloor>)"
    using Suc unfolding env_tran_right_def by fastforce
    have  k1:"k - 1 < k"
      by (metis (no_types) Suc_eq_plus1 j_1 lessI)    
    then have "(snd((snd (\<Gamma>,l))!(k-1)), snd((snd (\<Gamma>,l))!(Suc (k-1)))) \<in> 
                     (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (R ** tran_Id) \<rfloor>)"    
    using `j \<le> k - 1` f1 by blast                           
    ultimately have "snd (l!k) \<in> Normal ` (Collect q)" using stable_q_r_q Suc(2)  Suc(5)  by fastforce
    also have "fst (l!j) = fst (l!k)"
    proof -
      have "\<Gamma>\<turnstile>\<^sub>c (l ! (k-1)) \<rightarrow>\<^sub>e (l ! k)" using Suc(6) k1 `j\<le>k-1` by fastforce
      thus ?thesis using k1 prod.collapse env_c_c' induct by metis
    qed
    ultimately show ?case by meson
qed

lemma stable_only_env_i_j: 
  assumes a0:"Sta q (R \<and>* tran_Id)"  and                 
          a1: "snd(l!i) \<in> Normal ` (Collect q)" and
          a2: "i<j \<and> j < (length l)" and
          a3: "n=j-i-1" and
          a4: "\<forall>k\<ge>i. k < j \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))" and
          a5: "env_tran_right \<Gamma> l R"
      shows "snd (l!j) \<in> Normal ` (Collect q)"
using a0 a1 a2 a3 a4 a5  by (meson less_imp_le_nat  stability)

  
lemma stable_only_env_1: 
  assumes a0:"Sta q (R \<and>* tran_Id)"  and                 
          a1: "snd(l!i) \<in> Normal ` (Collect q)" and
          a2: "i<j \<and> j < (length l)" and
          a3: "n=j-i-1" and
          a4: "\<forall>i. Suc i < length l \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))" and
          a5: "env_tran_right \<Gamma> l R"
      shows "snd (l!j) \<in> Normal ` (Collect q)"
using a0 a1 a2 a3 a4 a5 
by (meson stable_only_env_i_j less_trans_Suc)


lemma stable_only_env_q: 
  assumes a0:"Sta q (R \<and>* tran_Id)"  and                 
          a1: "\<forall>i. Suc i < length l \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))" and
          a2: "env_tran \<Gamma> q l R"
      shows "\<forall>i. i < length l \<longrightarrow> snd (l!i) \<in> Normal ` (Collect q)"
proof (cases "0 < length l")
  case False thus ?thesis using a2 unfolding env_tran_def by fastforce 
next
  case True 
  thus ?thesis 
  proof - {
    fix i
    assume aa1:"i < length l"
    have post_0:"snd (l ! 0) \<in> Normal ` Collect q " 
      using a2 unfolding env_tran_def by auto
    then have "snd (l ! i) \<in> Normal ` Collect q"     
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
  "Sta q (R \<and>* tran_Id) \<Longrightarrow>       
   I \<triangleright> R \<Longrightarrow>
   I \<triangleright> G \<Longrightarrow>
   \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Skip sat [q,I, R, G, q,a]"
proof -  
 assume
    a0:"Sta q (R \<and>* tran_Id)" and    
    a2:"I \<triangleright> R" and
    a3:"I \<triangleright> G"
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
      {
       have cp:"l!0=(Skip,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
       have assum:"snd(l!0) \<in> Normal ` (Collect q) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                   (snd(l!i), snd(l!(Suc i))) \<in> 
                     (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (R ** tran_Id) \<rfloor>))" 
       using a11 c_prod unfolding assum_def by simp
       have concl:"(\<forall>i ns ns'. Suc i<length l \<longrightarrow> 
               \<Gamma>1\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow> 
               snd ((snd c)!(Suc i)) \<notin> Fault ` F  \<longrightarrow> 
               snd ((snd c)!i) = Normal ns \<and> snd ((snd c)!(Suc i)) = Normal ns' \<longrightarrow>              
                 (snd(l!i), snd(l!(Suc i))) \<in> 
                   (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>))"
       proof -
       { fix i
         assume asuc:"Suc i<length l"        
         then have "\<not> (\<Gamma>1\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))"
           by (metis Suc_lessD cp prod.collapse prod.sel(1) stepc_elim_cases(1) zero_skip_all_skip)
       } thus ?thesis by auto qed
       have concr:"(final (last l)  \<longrightarrow> 
                   snd (last l) \<notin> Fault ` F  \<longrightarrow>
                   ((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` (Collect q))) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (Collect a)))"
       proof-
       { 
         assume valid:"final (last l)"
         have len_l:"length l > 0" using cp using cptn.simps by blast 
         then obtain a l1 where l:"l=a#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
         have last_l:"last l = l!(length l-1)"
            using last_length [of a l1] l by fastforce
         then have fst_last_skip:"fst (last l) = Skip"             
           by (metis `0 < length l` cp diff_less fst_conv zero_less_one zero_skip_all_skip)                           
         have last_q: "snd (last l) \<in> Normal ` (Collect q)"    
         proof -
           have env: "env_tran \<Gamma> q l R" using env_tran_def assum cp by blast
           have env_right:"env_tran_right \<Gamma> l R" using env_tran_def env_tran_right_def assum cp by blast
           then have all_tran_env: "\<forall>i. Suc i < length l \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))"
           using final_always_env_i cp  by (simp add: cp zero_final_always_env_0)
           then have "\<forall>i. i < length l \<longrightarrow> snd (l!i) \<in> Normal ` (Collect q)"
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

lemma Throw_sound: "
       Sta a (R \<and>* tran_Id) \<Longrightarrow>
       I \<triangleright> R \<Longrightarrow>
       I \<triangleright> G \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Throw sat [a,I, R, G, q,a]"
proof -  
 assume   
    a1:"Sta a (R \<and>* tran_Id)" and
    a2:"I \<triangleright> R" and
    a3:"I \<triangleright> G"
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
      {
       have cp:"l!0=(Throw,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
       have assum:"snd(l!0) \<in> Normal ` (Collect a) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                   (snd(l!i), snd(l!(Suc i))) \<in> 
                     (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (R ** tran_Id) \<rfloor>))" 
       using a11 c_prod unfolding assum_def by simp
       then have env_tran:"env_tran_right \<Gamma> l R" using cp env_tran_right_def by auto
       have concl:"(\<forall>i ns ns'. Suc i<length l \<longrightarrow> 
               \<Gamma>1\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow> 
               snd ((snd c)!(Suc i)) \<notin> Fault ` F  \<longrightarrow> 
               snd ((snd c)!i) = Normal ns \<and> snd ((snd c)!(Suc i)) = Normal ns' \<longrightarrow>              
                 (snd(l!i), snd(l!(Suc i))) \<in> 
                   (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>))"
       proof -
       { fix i
         assume asuc:"Suc i<length l"
         then have asuci:"i<length l" by fastforce
         then have "fst (l ! 0) = LanguageCon.com.Throw" using cp by auto
         moreover obtain s1 where "snd (l ! 0) = Normal s1" using assum by auto
         ultimately have "fst (l ! i) = Throw \<and> (\<exists>s2. snd (l ! i) = Normal s2)"      
             using cp assum env_tran asuci zero_throw_all_throw by blast
         then have "\<not> (\<Gamma>1\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))"
           by (meson SmallStepCon.final_def SmallStepCon.no_step_final')           
       } thus ?thesis by auto qed
       have concr:"(final (last l)  \<longrightarrow> 
                   snd (last l) \<notin> Fault ` F  \<longrightarrow>
                   ((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` (Collect q))) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (Collect a)))"
       proof-
       { 
         assume valid:"final (last l)"
         have len_l:"length l > 0" using cp using cptn.simps by blast 
         then obtain a1 l1 where l:"l=a1#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
         have last_l:"last l = l!(length l-1)"
            using last_length [of a1 l1] l by fastforce
         then have fst_last_skip:"fst (last l) = Throw"
            by (metis (no_types, lifting) One_nat_def assum cp diff_Suc_less env_tran fst_conv imageE len_l zero_throw_all_throw)                        
         have last_q: "snd (last l) \<in> Normal ` (Collect a)"    
         proof -
           have env: "env_tran \<Gamma> a l R" using env_tran_def assum cp by blast
           have env_right:"env_tran_right \<Gamma> l R" using env_tran_def env_tran_right_def assum cp by blast
           then have all_tran_env: "\<forall>i. Suc i < length l \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))"
           using final_always_env_i  assum cp zero_final_always_env_0 by fastforce            
           then have "\<forall>i. i < length l \<longrightarrow> snd (l!i) \<in> Normal ` (Collect a)"
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
         a6: "env_tran_right \<Gamma> l rely"
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
      thus ?thesis using only_one_component_tran_j suc_0_skip a6 a0 a2 a3 by blast       
    qed
qed

lemma no_comp_tran_before_i:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = c" and        
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)))" and
         a3: "k\<le>j \<and> j < i \<and> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))" and
         a4: "\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))" and
         a5: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> ((c1=Skip)\<or> ((c1=Throw) \<and> (\<exists>s21. s2 = Normal s21)))" and
         a6: "env_tran_right \<Gamma> l rely"
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
  moreover have "env_tran_right \<Gamma> l1 rely" using Suc(8) l unfolding env_tran_right_def by fastforce
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
         a5: "env_tran_right \<Gamma> l rely"
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
         a5: "env_tran_right \<Gamma> l rely"
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
         a5: "env_tran_right \<Gamma> l rely"
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
         a4: "env_tran_right \<Gamma> l rely"
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
         a4: "env_tran_right \<Gamma> l rely"
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
          a2: "env_tran \<Gamma> q l R" and
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
          a4: "env_tran_right \<Gamma> l R"            
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
         a5: "env_tran_right \<Gamma> l rely" 
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
         a4: "env_tran_right \<Gamma> l rely"       
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
         a4: "env_tran_right \<Gamma> l rely"       
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
         a3: "env_tran_right \<Gamma> l rely"       
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
         a3: "env_tran_right \<Gamma> l rely"       
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Basic f,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  basic_skip by blast
  thus ?thesis using  a0 a1 a2 a3 only_one_component_tran_all_not_comp by blast
qed   

lemma final_exist_component_tran_basic:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
          a1: "fst (l!i) = Basic f" and               
          a2: "env_tran \<Gamma> q l R" and
          a3: "i\<le>j \<and> j < length l \<and> final (l!j)" 
  shows "\<exists>k. k\<ge>i \<and> k<j \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
proof - 
  show ?thesis using  a0 a1 a2 a3 final_exist_component_tran by blast
qed   

lemma Basic_sound: 
       "Collect p \<subseteq> {s. f s \<in> (Collect q)} \<Longrightarrow>
       \<forall>s t. ((p or (q or a)) imp (I\<and>*sep_true)) (s,t) \<Longrightarrow>
       \<forall>s t. ((p \<unrhd> q) imp (G\<and>*tran_True)) (s,t) \<Longrightarrow>
       Sta p (R\<and>*tran_Id) \<Longrightarrow>
       Sta q (R\<and>*tran_Id) \<Longrightarrow>
       I  \<triangleright> R \<Longrightarrow> I  \<triangleright> G \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  (Basic f) sat [p, I, R, G, q,a]"
proof -  
 assume
    a0:"Collect p \<subseteq> {s. f s \<in> (Collect q)}" and
    a1:"\<forall>s t. ((p or (q or a)) imp (I\<and>*sep_true)) (s,t)" and
    a2:"\<forall>s t. ((p \<unrhd> q) imp (G\<and>*tran_True)) (s,t)" and
    a3:"Sta p (R\<and>*tran_Id)" and
    a4:"Sta q (R\<and>*tran_Id)" and
    a6:"I  \<triangleright> R" and 
    a7:"I  \<triangleright> G" 
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
       have assum:"snd(l!0) \<in> Normal ` (Collect p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                   (snd(l!i), snd(l!(Suc i))) \<in> 
                     (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (R ** tran_Id) \<rfloor>))" 
       using a11 c_prod unfolding assum_def by simp
       have concl:"(\<forall>i ns ns'. Suc i<length l \<longrightarrow> 
               \<Gamma>1\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow> 
               snd ((snd c)!i) = Normal ns \<and> snd ((snd c)!(Suc i)) = Normal ns' \<longrightarrow>                             
               (snd(l!i), snd(l!(Suc i))) \<in> 
                 (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>))"
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
           using env_tran env_tran_right_def unfolding env_tran_def by auto
         then have all_event:"\<forall>j. 0\<le>j \<and> j \<noteq> k \<and> Suc j < length l \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
           using a00 a11  only_one_component_tran_all_env_basic[of \<Gamma> l 0 f k R] env_tran_right cp len_l
           by fastforce
         then have before_k_all_evn:"\<forall>j. 0\<le>j \<and> j < k  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
               using a00 a11  by fastforce
         then have k_basic:"fst(l!k) = Basic f \<and> snd (l!k) \<in> Normal ` (Collect p)" 
           using  cp env_tran_right a3 assum a00 a11  stability[of p R l 0 k k \<Gamma>]
           by force
         have suc_k_skip_q:"fst(l!Suc k) = Skip \<and> snd (l!(Suc k)) \<in> Normal ` (Collect q)"
         proof 
           show suc_skip: "fst(l!Suc k) = Skip"
             using a0 a00 a11  k_basic by (metis basic_skip surjective_pairing) 
         next
           obtain s' where k_s: "snd (l!k)=Normal s' \<and> s' \<in> (Collect p)" 
             using a00 a11  k_basic by auto
           then have "snd (l!(Suc k)) = Normal (f s')"          
             using a00 a11  k_basic stepc_Normal_elim_cases(3)
             by (metis prod.inject surjective_pairing)          
           then show "snd (l!(Suc k)) \<in> Normal ` (Collect q)" using a0 k_s by blast
         qed
         obtain s' s'' where ss:"snd (l!k) = Normal s' \<and> s' \<in> (Collect p) \<and>  snd (l!(Suc k)) = Normal s'' \<and> s'' \<in> (Collect q)"
           using suc_k_skip_q k_basic by fastforce
         then have "(p \<unrhd> q)(s',s'')" unfolding after_def by auto
         then have "(snd(l!k), snd(l!(Suc k))) \<in> 
                   (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>)"
           using ss a2 unfolding Satis_def
           proof -
             have "(G \<and>* tran_True) (s', s'')"
                by (metis `(p \<unrhd> q) (s', s'')` a2)
             thus "(snd (l ! k), snd (l ! Suc k)) \<in> (\<lambda>(pa, p). (Normal pa, Normal p)) ` Collect (G \<and>* tran_True)"
                using ss by force
           qed 
       } thus ?thesis by auto qed
       have concr:"(final (last l)  \<longrightarrow> 
                   snd (last l) \<notin> Fault ` F  \<longrightarrow>
                   ((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` (Collect q))) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (Collect a)))"
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
           moreover have "fst (l!0) = Basic f" using cp by auto
           ultimately show ?thesis 
             using cp final_exist_component_tran_basic env_tran by blast 
         qed
         then obtain k where k_comp_tran: "k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
           by auto
         then have all_event:"\<forall>j. 0\<le>j \<and> j \<noteq> k \<and> Suc j < length l \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
           using only_one_component_tran_all_env_basic[of \<Gamma> l 0 f k R] env_tran_right cp len_l
           by fastforce
         then have before_k_all_evn:"\<forall>j. 0\<le>j \<and> j < k  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
               using k_comp_tran by fastforce
         then have k_basic:"fst(l!k) = Basic f \<and> snd (l!k) \<in> Normal ` (Collect p)" 
           using  cp env_tran_right a3 assum k_comp_tran stability[of p R l 0 k k \<Gamma>]
           by force
         have suc_k_skip_q:"fst(l!Suc k) = Skip \<and> snd (l!(Suc k)) \<in> Normal ` (Collect q)"
         proof 
           show suc_skip: "fst(l!Suc k) = Skip"
             using a0 k_comp_tran k_basic by (metis basic_skip surjective_pairing) 
         next
           obtain s' where k_s: "snd (l!k)=Normal s' \<and> s' \<in> (Collect p)" 
             using k_comp_tran k_basic by auto
           then have "snd (l!(Suc k)) = Normal (f s')"          
             using k_comp_tran k_basic stepc_Normal_elim_cases(3)
             by (metis prod.inject surjective_pairing)          
           then show "snd (l!(Suc k)) \<in> Normal ` (Collect q)" using a0 using k_s by blast
         qed
         have after_k_all_evn:"\<forall>j. (Suc k)\<le>j \<and> Suc j < (length l)  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
               using all_event k_comp_tran by fastforce                            
         then have fst_last_skip:"fst (last l) = Skip \<and> 
                             snd ((last l)) \<in> Normal ` (Collect q)"
         using  last_l len_l cp env_tran_right a4 suc_k_skip_q assum k_comp_tran stability [of q R l "Suc k" "((length l) - 1)" _ \<Gamma>] 
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
         a5: "env_tran_right \<Gamma> l rely" 
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
         a4: "env_tran_right \<Gamma> l rely"       
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
         a4: "env_tran_right \<Gamma> l rely"       
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
         a3: "env_tran_right \<Gamma> l rely"       
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
         a3: "env_tran_right \<Gamma> l rely"       
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  spec_skip by blast
  thus ?thesis using  a0 a1 a2 a3 only_one_component_tran_all_not_comp by blast
qed   

lemma final_exist_component_tran_spec:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
          a1: "fst (l!i) = Spec r" and               
          a2: "env_tran \<Gamma> q l R" and
          a3: "i\<le>j \<and> j < length l \<and> final (l!j)" 
  shows "\<exists>k. k\<ge>i \<and> k<j \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  spec_skip by blast
  thus ?thesis using  a0 a1 a2 a3 final_exist_component_tran by blast
qed   

lemma Spec_sound: 
       "Collect p \<subseteq> {s. (\<forall>t. (s,t)\<in>r \<longrightarrow> t \<in> Collect q) \<and> (\<exists>t. (s,t) \<in> r)} \<Longrightarrow>
       \<forall>s t. ((p or (q or a)) imp (I\<and>*sep_true)) (s,t) \<Longrightarrow>
       \<forall>s t. ((p \<unrhd> q) imp (G\<and>*tran_True)) (s,t) \<Longrightarrow>
       Sta p (R\<and>*tran_Id) \<Longrightarrow>
       Sta q (R\<and>*tran_Id) \<Longrightarrow>       
       I  \<triangleright> R \<Longrightarrow> I  \<triangleright> G \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  (Spec r) sat [p, I, R, G, q,a]"
proof -  
 assume
    a0:"Collect p \<subseteq> {s. (\<forall>t. (s,t)\<in>r \<longrightarrow> t \<in> Collect q) \<and> (\<exists>t. (s,t) \<in> r)}" and
    a1:"\<forall>s t. ((p or (q or a)) imp (I\<and>*sep_true)) (s,t)" and
    a2:"\<forall>s t. ((p \<unrhd> q) imp (G\<and>*tran_True)) (s,t)" and
    a3:"Sta p (R\<and>*tran_Id)" and
    a4:"Sta q (R\<and>*tran_Id)" and   
    a6:"I  \<triangleright> R" and 
    a7:"I  \<triangleright> G" 
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
       have assum:"snd(l!0) \<in> Normal ` (Collect p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                   (snd(l!i), snd(l!(Suc i))) \<in> 
                     (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (R ** tran_Id) \<rfloor>))" 
       using a11 c_prod unfolding assum_def by simp
       have concl:"(\<forall>i ns ns'. Suc i<length l \<longrightarrow> 
               \<Gamma>1\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow> 
               snd ((snd c)!i) = Normal ns \<and> snd ((snd c)!(Suc i)) = Normal ns' \<longrightarrow>                              
                 (snd(l!i), snd(l!(Suc i))) \<in> 
                   (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>))"
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
           using a00 a11  only_one_component_tran_all_env_spec[of \<Gamma> l 0 r k R] env_tran_right cp len_l
           by fastforce
         then have before_k_all_evn:"\<forall>j. 0\<le>j \<and> j < k  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
               using a00 a11  by fastforce
         then have k_basic:"ck = Spec r \<and> sk \<in> Normal ` (Collect p)" 
           using  cp env_tran_right a3 assum a00 a11 stability[of p R l 0 k k \<Gamma>] tran_pair
           by force
         have suc_skip: "csk = Skip"
            using a0 a00 k_basic tran_pair spec_skip by blast
         have suc_k_skip_q:"ssk \<in> Normal ` (Collect q)"           
         proof -         
           obtain s' where k_s: "sk =Normal s' \<and> s' \<in> (Collect p)" 
             using k_basic by auto
           then obtain t where "ssk = Normal t" 
           using step_spec_skip_normal_normal[of \<Gamma>1 ck sk csk ssk r s'] k_basic tran_pair a0 suc_skip
           by blast           
           then obtain t where "ssk= Normal t" by fastforce
           then have "(s',t)\<in>r" using a0 k_basic k_s a11 suc_skip 
             by (metis (no_types, lifting)  stepc_Normal_elim_cases(4) tran_pair prod.inject xstate.distinct(5) xstate.inject(1))
           thus "ssk \<in> Normal ` Collect q"  using a0 k_s `ssk = Normal t` by blast 
         qed                                                      
         obtain s' s'' where ss:"sk = Normal s' \<and> s' \<in> (Collect p) \<and>  ssk = Normal s'' \<and> s'' \<in> (Collect q)"
           using suc_k_skip_q k_basic by fastforce
         then have "(p \<unrhd> q)(s',s'')" unfolding after_def by auto
         then have "(snd(l!k), snd(l!(Suc k))) \<in> 
                   (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>)"
           using ss a2 unfolding Satis_def
           proof -
             have "(G \<and>* tran_True) (s', s'')"
                by (metis `(p \<unrhd> q) (s', s'')` a2)
             thus "(snd (l ! k), snd (l ! Suc k)) \<in> (\<lambda>(pa, p). (Normal pa, Normal p)) ` Collect (G \<and>* tran_True)"
                using ss tran_pair by force
           qed 
       } thus ?thesis by auto qed
       have concr:"(final (last l)  \<longrightarrow> ((fst (last l) = Skip \<and> 
                                                  snd (last l) \<in> Normal ` (Collect q))) \<or>
                                                  (fst (last l) = Throw \<and> 
                                                  snd (last l) \<in> Normal ` (Collect a)))"
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
             using cp final_exist_component_tran_spec env_tran by blast 
         qed
         then obtain k  where k_comp_tran: "k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
           by auto
         then obtain ck sk csk ssk where tran_pair:
           "\<Gamma>1\<turnstile>\<^sub>c (ck,sk)  \<rightarrow> (csk, ssk) \<and> (ck = fst (l!k)) \<and> (sk = snd (l!k)) \<and> (csk = fst (l!(Suc k))) \<and> (ssk = snd (l!(Suc k)))" 
           using cp by fastforce
         then have all_event:"\<forall>j. 0\<le>j \<and> j \<noteq> k \<and> Suc j < length l \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
           using  k_comp_tran only_one_component_tran_all_env_spec[of \<Gamma> l 0 r k R] env_tran_right cp len_l
           by fastforce
         then have before_k_all_evn:"\<forall>j. 0\<le>j \<and> j < k  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
               using k_comp_tran by fastforce
         then have k_basic:"ck = Spec r \<and> sk \<in> Normal ` (Collect p)" 
           using  cp env_tran_right a3 assum tran_pair k_comp_tran stability[of p R l 0 k k \<Gamma>] tran_pair
           by force
         have suc_skip: "csk = Skip"
            using a0  k_basic tran_pair spec_skip by blast
         have suc_k_skip_q:"ssk \<in> Normal ` (Collect q)"           
         proof -         
           obtain s' where k_s: "sk =Normal s' \<and> s' \<in> (Collect p)" 
             using k_basic by auto
           then obtain t where "ssk = Normal t" 
           using step_spec_skip_normal_normal[of \<Gamma>1 ck sk csk ssk r s'] k_basic tran_pair a0 suc_skip
           by blast           
           then obtain t where "ssk= Normal t" by fastforce
           then have "(s',t)\<in>r" using a0 k_basic k_s a11 suc_skip 
             by (metis (no_types, lifting)  stepc_Normal_elim_cases(4) tran_pair prod.inject xstate.distinct(5) xstate.inject(1))
           thus "ssk \<in> Normal ` Collect q"  using a0 k_s `ssk = Normal t` by blast 
         qed    
         have after_k_all_evn:"\<forall>j. (Suc k)\<le>j \<and> Suc j < (length l)  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
               using all_event k_comp_tran by fastforce                            
         then have fst_last_skip:"fst (last l) = Skip \<and> 
                             snd ((last l)) \<in> Normal ` (Collect q)"
         using l tran_pair suc_skip last_l len_l cp 
               env_tran_right a4 suc_k_skip_q 
               assum k_comp_tran stability [of q R l "Suc k" "((length l) - 1)" _ \<Gamma>] 
         by (metis One_nat_def Suc_eq_plus1 Suc_leI Suc_mono diff_Suc_1 lessI list.size(4))                  
       } thus ?thesis by auto qed
       note res = conjI [OF concl concr]               
      }              
      thus ?thesis using c_prod unfolding comm_def by auto qed      
    } thus ?thesis by auto qed 
  } thus ?thesis by (simp add: com_validity_def[of \<Gamma>] com_cvalidity_def)
qed

subsection {* Spec Sound *}

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
         a5: "env_tran_right \<Gamma> l rely" 
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
         a4: "env_tran_right \<Gamma> l rely"       
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
         a4: "env_tran_right \<Gamma> l rely"       
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
         a3: "env_tran_right \<Gamma> l rely"       
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
         a3: "env_tran_right \<Gamma> l rely"       
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)\<or>(c1 = Throw \<and> (\<exists>s21. s2 =Normal s21 ))" 
    using  await_skip by blast
  thus ?thesis using  a0 a1 a2 a3 only_one_component_tran_all_not_comp by blast
qed   

lemma final_exist_component_tran_await:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
          a1: "fst (l!i) = Await b c" and               
          a2: "env_tran \<Gamma> q l R" and
          a3: "i\<le>j \<and> j < length l \<and> final (l!j)" 
  shows "\<exists>k. k\<ge>i \<and> k<j \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)\<or>(c1 = Throw \<and> (\<exists>s21. s2 =Normal s21 ))" 
    using  await_skip by blast
  thus ?thesis using  a0 a1 a2 a3 final_exist_component_tran by blast
qed   

lemma Await_sound: 
       "\<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> (Collect p \<inter> b) e (Collect q),(Collect a) \<Longrightarrow>
       \<forall>s t. ((p or (q or a)) imp (I\<and>*sep_true)) (s,t) \<Longrightarrow>
       \<forall>s t. ((p \<unrhd> (q or a)) imp (G\<and>*tran_True)) (s,t) \<Longrightarrow>
       Sta p (R\<and>*tran_Id) \<Longrightarrow>
       Sta q (R\<and>*tran_Id) \<Longrightarrow>
       Sta a (R\<and>*tran_Id) \<Longrightarrow>
       I  \<triangleright> R \<Longrightarrow> I  \<triangleright> G \<Longrightarrow>
       \<Gamma>,\<Theta>\<Turnstile>\<^bsub>/F\<^esub> (Await b e) sat [p, I, R, G, q,a]"
proof -  
 assume
    a0: "\<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> (Collect p \<inter> b) e (Collect q),(Collect a)" and
    a1:"\<forall>s t. ((p or (q or a)) imp (I\<and>*sep_true)) (s,t)" and
    a2:"\<forall>s t. ((p \<unrhd> (q or a)) imp (G\<and>*tran_True)) (s,t)" and
    a3:"Sta p (R\<and>*tran_Id)" and
    a4:"Sta q (R\<and>*tran_Id)" and
    a5:"Sta a (R\<and>*tran_Id)" and
    a6:"I  \<triangleright> R" and 
    a7:"I  \<triangleright> G" 
{
    fix s
    assume all_call:"\<forall>(c,p,I,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, I , R, G, q,a]"
    have "cp \<Gamma> (Await b e) s \<inter> assum(p, R) F \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cp \<Gamma> (Await b e) s" and a11:"c \<in> assum(p, R) F"
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof - 
      {
       have cp:"l!0=(Await b e,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
       have assum:"snd(l!0) \<in> Normal ` (Collect p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                   (snd(l!i), snd(l!(Suc i))) \<in> 
                     (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (R ** tran_Id) \<rfloor>))" 
       using a11 c_prod unfolding assum_def by simp
       have concl:"(\<forall>i ns ns'. Suc i<length l \<longrightarrow> 
               \<Gamma>1\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow>
               snd (l!i) = Normal ns \<and> snd (l!(Suc i)) = Normal ns' \<longrightarrow>                              
                 (snd(l!i), snd(l!(Suc i))) \<in> 
                   (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>))"
       proof -
       { fix k ns ns'
         assume a00:"Suc k<length l" and
                a11:"\<Gamma>1\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))"and
                a22:"snd (l!k) = Normal ns \<and> snd (l!(Suc k)) = Normal ns'"
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
           using a00 a11  only_one_component_tran_all_env_await[of \<Gamma> l 0 b e k R] env_tran_right cp len_l
           by fastforce
         then have before_k_all_evn:"\<forall>j. 0\<le>j \<and> j < k  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
               using a00 a11  by fastforce
         then have k_basic:"ck = Await b e \<and> sk \<in> Normal ` (Collect p)" 
           using  cp env_tran_right a3 assum a00 a11 a22 stability[of p R l 0 k k \<Gamma>] tran_pair
           by force
         have suc_skip: "csk = Skip  \<or> (csk = Throw \<and> (\<exists>s1. ssk = Normal s1))"
            using a0 a00 k_basic tran_pair await_skip by blast
         have suc_k_skip_q:"ssk \<in> Normal ` (Collect q) \<or> ssk \<in> Normal ` (Collect a)"           
         proof -         
           obtain s' where k_s: "sk =Normal s' \<and> s' \<in> (Collect p)" 
             using k_basic by auto
           then obtain t where ssk_normal:"ssk = Normal t" 
           using  k_basic tran_pair a0 a22  by auto               
           have "\<Gamma>\<^sub>\<not>\<^sub>a,{}\<Turnstile>\<^bsub>/F\<^esub> (Collect p \<inter> b) e (Collect q),(Collect a)"
           using  a0 hoare_sound 
             by fastforce
           then have e_auto:"\<Gamma>\<^sub>\<not>\<^sub>a,{}\<Turnstile>\<^bsub>/F\<^esub> (Collect p \<inter> b) e (Collect q),(Collect a)" 
             unfolding cvalid_def by auto
           have "csk = Skip  \<or> csk = Throw" using suc_skip by auto
           thus ?thesis
           proof
             assume "csk = LanguageCon.com.Skip"
             then have "\<Gamma>\<^sub>\<not>\<^sub>a\<turnstile>\<langle>e,sk\<rangle> \<Rightarrow> Normal t"
               using k_s tran_pair k_basic ssk_normal cp stepc_elim_cases_Await_skip 
               by metis 
             also have "sk \<in> Normal ` (Collect p \<inter> b)" 
               using k_s tran_pair k_basic ssk_normal cp
               by (metis IntI image_eqI stepc_Normal_elim_cases(8))
             ultimately show ?thesis  
               using e_auto ssk_normal unfolding valid_def cvalid_def by blast
           next
             assume "csk = LanguageCon.com.Throw"
             then have "\<Gamma>\<^sub>\<not>\<^sub>a\<turnstile>\<langle>e,sk\<rangle> \<Rightarrow> Abrupt t"
               using k_s tran_pair k_basic ssk_normal cp stepc_elim_cases_Await_throw xstate.inject(1)
               by metis                
             also have "sk \<in> Normal ` (Collect p \<inter> b)" 
               using k_s tran_pair k_basic ssk_normal cp
               by (metis IntI image_eqI stepc_Normal_elim_cases(8))
             ultimately show ?thesis  
               using e_auto ssk_normal unfolding valid_def cvalid_def by blast
           qed            
         qed                                                      
         obtain s' s'' where ss:
           "sk = Normal s' \<and> s' \<in> (Collect p) \<and>  ssk = Normal s'' 
            \<and> (s'' \<in> (Collect q) \<or> s''\<in> (Collect a))"
           using suc_k_skip_q k_basic  by fastforce
         then have "(p \<unrhd> (q or a))(s',s'')" unfolding after_def by auto
         then have "(snd(l!k), snd(l!(Suc k))) \<in> 
                   (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>)"
           using ss a2 unfolding Satis_def
           proof -
             have "(G \<and>* tran_True) (s', s'')"
                by (metis `(p \<unrhd> (q or a)) (s', s'')` a2)
             thus "(snd (l ! k), snd (l ! Suc k)) \<in> (\<lambda>(pa, p). (Normal pa, Normal p)) ` Collect (G \<and>* tran_True)"
                using ss tran_pair by force
           qed 
       } thus ?thesis using c_prod by auto qed  
       have concr:"(final (last l)  \<longrightarrow> 
                   snd (last l) \<notin> Fault ` F  \<longrightarrow>
                   ((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` (Collect q))) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (Collect a)))"
       proof-
       { 
         assume valid:"final (last l)"
         assume last_fault:"snd (last l) \<notin> Fault ` F"
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
             using cp final_exist_component_tran_await env_tran by blast 
         qed
         then obtain k  where k_comp_tran: "k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
           by auto
         then obtain ck sk csk ssk where tran_pair:
           "\<Gamma>1\<turnstile>\<^sub>c (ck,sk)  \<rightarrow> (csk, ssk) \<and> (ck = fst (l!k)) \<and> (sk = snd (l!k)) \<and> (csk = fst (l!(Suc k))) \<and> (ssk = snd (l!(Suc k)))" 
           using cp by fastforce
         then have all_event:"\<forall>j. 0\<le>j \<and> j \<noteq> k \<and> Suc j < length l \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
           using  k_comp_tran only_one_component_tran_all_env_await[of \<Gamma> l 0 b e k R] env_tran_right cp len_l
           by fastforce
         then have before_k_all_evn:"\<forall>j. 0\<le>j \<and> j < k  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
               using k_comp_tran by fastforce
         then have k_basic:"ck = Await b e \<and> sk \<in> Normal ` (Collect p)" 
           using  cp env_tran_right a3 assum tran_pair k_comp_tran stability[of p R l 0 k k \<Gamma>] tran_pair
           by force        
         have "\<Gamma>\<^sub>\<not>\<^sub>a,{}\<Turnstile>\<^bsub>/F\<^esub> (Collect p \<inter> b) e (Collect q),(Collect a)"
           using  a0 hoare_sound 
             by fastforce
         then have e_auto:"\<Gamma>\<^sub>\<not>\<^sub>a\<Turnstile>\<^bsub>/F\<^esub> (Collect p \<inter> b) e (Collect q),(Collect a)" 
           unfolding cvalid_def by auto
         have after_k_all_evn:"\<forall>j. (Suc k)\<le>j \<and> Suc j < (length l)  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
               using all_event k_comp_tran by fastforce 
         obtain s' where k_s: "sk =Normal s' \<and> s' \<in> (Collect p)" 
             using k_basic by auto
         have suc_skip: "csk = Skip  \<or> (csk = Throw \<and> (\<exists>s1. ssk = Normal s1))"
            using a0  k_basic tran_pair await_skip by blast
         moreover {
           assume at:"csk = Skip" 
           then have atom_tran:"\<Gamma>\<^sub>\<not>\<^sub>a\<turnstile>\<langle>e,sk\<rangle> \<Rightarrow> ssk"
               using k_s tran_pair k_basic cp stepc_elim_cases_Await_skip
               by metis
           have sk_in_normal_pb:"sk \<in> Normal ` (Collect p \<inter> b)" 
               using k_s tran_pair k_basic cp
               by (metis IntI image_eqI stepc_Normal_elim_cases(8))                                  
           then have "fst (last l) = Skip \<and> 
                       snd ((last l)) \<in> Normal ` (Collect q)" 
           proof (cases ssk)
             case (Normal t)                                                  
             then have "ssk \<in> Normal ` Collect q" 
               using sk_in_normal_pb e_auto Normal atom_tran unfolding valid_def
               by blast
             thus ?thesis
               using at l tran_pair last_l len_l cp 
                 env_tran_right a4  after_k_all_evn
                 assum k_comp_tran stability [of q R l "Suc k" "((length l) - 1)" _ \<Gamma>]         
               by (metis One_nat_def Suc_eq_plus1 Suc_leI Suc_mono diff_Suc_1 lessI list.size(4))
           next
              case (Abrupt t)
              thus ?thesis 
               using at k_s tran_pair k_basic cp stepc_elim_cases_Await_skip
                 by metis                
           next
              case (Fault f1)              
              then have "ssk \<in> Normal ` Collect q \<or> ssk \<in> Fault ` F" 
                using sk_in_normal_pb e_auto Fault atom_tran unfolding valid_def by auto                          
              thus ?thesis
              proof
                assume "ssk \<in> Normal ` Collect q" thus ?thesis using Fault by auto
              next
                assume suck_fault:"ssk \<in> Fault ` F"
                 have f1: "Suc k < length l" using k_comp_tran len_l
                 by fastforce
                 have "env_tran_right \<Gamma>1 l R"
                   using cp env_tran_right by blast
                 then have "Suc k=length l -1" 
                   using f1  skip_fault_last[of \<Gamma>1 l "Suc k" ssk R] at 
                     cp local.Fault prod.collapse tran_pair xstate.distinct(3) 
                   by metis
                 thus ?thesis using at last_l last_fault suck_fault tran_pair
                   by auto
              qed
           next 
              case (Stuck)             
              then have "ssk \<in> Normal ` Collect q" 
               using sk_in_normal_pb e_auto Stuck atom_tran unfolding valid_def
               by blast
              thus ?thesis using Stuck by auto                             
           qed            
         }
         moreover {
           assume at:"(csk = Throw \<and> (\<exists>t. ssk = Normal t))"
           then obtain t where ssk_normal:"ssk=Normal t" by auto
           then have atom_tran:"\<Gamma>\<^sub>\<not>\<^sub>a\<turnstile>\<langle>e,sk\<rangle> \<Rightarrow> Abrupt t"
               using at k_s tran_pair k_basic ssk_normal cp stepc_elim_cases_Await_throw xstate.inject(1)
               by metis                        
           also have "sk \<in> Normal ` (Collect p \<inter> b)" 
               using k_s tran_pair k_basic ssk_normal cp
               by (metis IntI image_eqI stepc_Normal_elim_cases(8))
           then have "ssk \<in> Normal ` Collect a" 
             using e_auto ssk_normal atom_tran unfolding valid_def
             by blast
           then have "(fst (last l) = Throw \<and> snd (last l) \<in> Normal ` (Collect a))"
           using at l tran_pair last_l len_l cp 
               env_tran_right a5  after_k_all_evn
               assum k_comp_tran stability [of a R l "Suc k" "((length l) - 1)" _ \<Gamma>]         
           by (metis One_nat_def Suc_eq_plus1 Suc_leI Suc_mono diff_Suc_1 lessI list.size(4))           
         }
         ultimately have "fst (last l) = Skip \<and> 
                             snd ((last l)) \<in> Normal ` (Collect q) \<or>
                            (fst (last l) = Throw \<and> snd (last l) \<in> Normal ` (Collect a))"
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
  a1: "k < length l \<and> l!k=(c1,Normal s') \<and> p1 s'"
shows "(\<Gamma>,drop k l)\<in> ((cp \<Gamma> c1 (Normal s')) \<inter> assum(p1, R) F)"
proof -
  have drop_k_s:"(drop k l)!0 = (c1,Normal s')" using a1 by fastforce
  have p1:"p1 s'" using a1 by auto
  have k_l:"k < length l" using a1 by auto
  show ?thesis
  proof
    show "(\<Gamma>, drop k l) \<in> cp \<Gamma> c1 (Normal s')" 
    unfolding cp_def 
    using dropcptn_is_cptn a0 a1 drop_k_s cp_def 
    by fastforce
  next
    let ?c= "(\<Gamma>,drop k l)"
    have l:"snd((snd ?c!0)) \<in> Normal ` (Collect p1)"
     using p1 drop_k_s by auto
    {fix i
     assume a00:"Suc i<length (snd ?c)" 
     assume a11:"(fst ?c)\<turnstile>\<^sub>c((snd ?c)!i)  \<rightarrow>\<^sub>e ((snd ?c)!(Suc i))"
     have "(snd((snd ?c)!i), snd((snd ?c)!(Suc i))) \<in> 
            (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (R \<and>* tran_Id) \<rfloor>)"
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
shows "(Suc k < length l \<longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)) \<longrightarrow> 
       snd (l!k) = Normal ns \<and> snd (l!(Suc k)) = Normal ns'\<longrightarrow>
       (snd(l!k), snd(l!(Suc k))) \<in> 
          (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G \<and>* tran_True) \<rfloor>))
       \<and> (final (last (l))  \<longrightarrow> 
          snd (last (l)) \<notin> Fault ` F  \<longrightarrow>
            ((fst (last (l)) = Skip \<and> 
              snd (last (l)) \<in> Normal ` (Collect q))) \<or>
            (fst (last (l)) = Throw \<and> 
              snd (last (l)) \<in> Normal ` (Collect a)))"
proof -  
  have pair_\<Gamma>l:"fst (\<Gamma>,l1) = \<Gamma> \<and> snd (\<Gamma>,l1) = l1" by fastforce  
  have a03:"(\<forall>i ns ns'.                 
               Suc i<length (snd (\<Gamma>, l1)) \<longrightarrow> 
               fst (\<Gamma>, l1)\<turnstile>\<^sub>c((snd (\<Gamma>, l1))!i)  \<rightarrow> ((snd (\<Gamma>, l1))!(Suc i)) \<longrightarrow>
               snd ((snd (\<Gamma>, l1))!i) = Normal ns \<and> snd ((snd (\<Gamma>, l1))!(Suc i)) = Normal ns' \<longrightarrow>                               
                 (snd((snd (\<Gamma>, l1))!i), snd((snd (\<Gamma>, l1))!(Suc i))) \<in> 
                    (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G \<and>* tran_True) \<rfloor>)) \<and> 
               (final (last (snd (\<Gamma>, l1)))  \<longrightarrow> 
                snd (last (snd (\<Gamma>, l1))) \<notin> Fault ` F  \<longrightarrow>
                  ((fst (last (snd (\<Gamma>, l1))) = Skip \<and> 
                    snd (last (snd (\<Gamma>, l1))) \<in> Normal ` (Collect q))) \<or>
                  (fst (last (snd (\<Gamma>, l1))) = Throw \<and> 
                    snd (last (snd (\<Gamma>, l1))) \<in> Normal ` (Collect a)))"
  using a1 unfolding comm_def by fastforce
  show ?thesis  
  proof  
  { assume "Suc k < length l"
    then have a2: "k \<ge> j \<and> Suc k < length l" using a2 by auto
    have "k \<le> length l" using a2 by fastforce
    then have l1_l:"(l!k = l1! (k - j) ) \<and> (l!Suc k = l1!Suc (k - j))"
    using a1 a2 by fastforce    
    have a00:"Suc (k - j) < length l1" using a1 a2 by fastforce
    have "\<Gamma>\<turnstile>\<^sub>c(l1!(k-j))  \<rightarrow> (l1!(Suc (k-j))) \<longrightarrow> 
       snd (l1!(k-j)) = Normal ns \<and> snd (l1!(Suc (k-j))) = Normal ns'\<longrightarrow>
      (snd((snd (\<Gamma>, l1))!(k-j)), snd((snd (\<Gamma>, l1))!(Suc (k-j)))) \<in> 
                      (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G \<and>* tran_True) \<rfloor>)"
    using  pair_\<Gamma>l a00  a03 by presburger
    then have "\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)) \<longrightarrow> 
       snd (l!k) = Normal ns \<and> snd (l!(Suc k)) = Normal ns'\<longrightarrow>(snd (l ! k), snd (l ! Suc k)) \<in> 
            (\<lambda>(x, y). (Normal x, Normal y)) ` (\<lfloor> (G \<and>* tran_True) \<rfloor>) " 
    using l1_l by auto
    } thus "Suc k < length l \<longrightarrow>
    \<Gamma>\<turnstile>\<^sub>c l ! k \<rightarrow> l ! Suc k \<longrightarrow>
    snd (l ! k) = Normal ns \<and> snd (l ! Suc k) = Normal ns' \<longrightarrow>
    (snd (l ! k), snd (l ! Suc k))
    \<in> (\<lambda>(x, y). (Normal x, Normal y)) ` (\<lfloor> (G \<and>* tran_True) \<rfloor>)" by auto    
  next
    {
      assume a10:"final (last (l))" and
             a11: "snd (last (l)) \<notin> Fault ` F"
      then have final_eq: "final (last (l1)) \<and> snd (last (l1)) \<notin> Fault ` F"
        using a10 a11 a1 a2 by fastforce
      then have "((fst (last (snd (\<Gamma>, l1))) = Skip \<and> 
                        snd (last (snd (\<Gamma>, l1))) \<in> Normal ` (Collect q))) \<or>
                      (fst (last (snd (\<Gamma>, l1))) = Throw \<and> 
                        snd (last (snd (\<Gamma>, l1))) \<in> Normal ` (Collect a))"
     using pair_\<Gamma>l a03 by presburger
     then have "((fst (last (snd (\<Gamma>, l))) = Skip \<and> 
              snd (last (snd (\<Gamma>, l))) \<in> Normal ` (Collect q))) \<or>
              (fst (last (snd (\<Gamma>, l))) = Throw \<and> 
             snd (last (snd (\<Gamma>, l))) \<in> Normal ` (Collect a))"
     using final_eq a1 a2 by auto 
    } thus 
     "SmallStepCon.final (last l) \<longrightarrow>
      snd (last l) \<notin> Fault ` F \<longrightarrow>
      fst (last l) = LanguageCon.com.Skip \<and> snd (last l) \<in> Normal ` Collect q \<or>
     fst (last l) = LanguageCon.com.Throw \<and> snd (last l) \<in> Normal ` Collect a"
   by fastforce
  qed
qed


lemma If_sound: 
      "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p and (set_fun b), I, R, G, q,a] \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p and (set_fun b), I, R, G, q,a] \<Longrightarrow>
       \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [p and (not (set_fun b)), I, R, G, q,a] \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c2 sat [p and (not (set_fun b)), I, R, G, q,a] \<Longrightarrow>
       \<forall>s t. (p imp I) (s,t) \<Longrightarrow>  
       Sta p (R\<and>*tran_Id) \<Longrightarrow>     
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> (Cond b c1 c2) sat [p, I, R, G, q,a]"
proof -  
 assume
    a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p and (set_fun b), I, R, G, q,a]" and
    a1:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [p and (not (set_fun b)), I, R, G, q,a]" and
    a2: "\<forall>s t. (p imp I) (s,t)" and
    a3:  "\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p and (set_fun b), I, R, G, q,a]" and
    a4: "\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c2 sat [p and (not (set_fun b)), I, R, G, q,a]" and
    a5: "Sta p (R\<and>*tran_Id)"
  then have orig_rule:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Cond b c1 c2) sat [p, I, R, G, q,a]" using lrghoare.If
  by blast 
  then have I_fence_G:
    "(I  \<triangleright> G) \<and> (I \<triangleright> R) 
     \<and> (\<forall>s t. ((p or (q or a)) imp (I\<and>*sep_true)) (s,t))"  
    using satis_wellformed by blast  
  { 
    fix s
    assume all_call:"\<forall>(c,p,I,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, I , R, G, q,a]"
    then have a4:"\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c2 sat [p and (not (set_fun b)), I, R, G, q,a]" 
      using a4 com_cvalidity_def by fastforce 
    have a3:"\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p and (set_fun b), I, R, G, q,a]"
      using a3 all_call com_cvalidity_def by fastforce 
    have "cp \<Gamma> (Cond b c1 c2)  s \<inter> assum(p, R) F \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cp \<Gamma> (Cond b c1 c2) s" and a11:"c \<in> assum(p, R) F"
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof - 
      {
       have cp:"l!0=((Cond b c1 c2),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
       have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast
       have assum:"snd(l!0) \<in> Normal ` (Collect p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                   (snd(l!i), snd(l!(Suc i))) \<in> 
                     (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (R ** tran_Id) \<rfloor>))" 
       using a11 c_prod unfolding assum_def by simp
       then have env_tran:"env_tran \<Gamma> p l R" using env_tran_def cp by blast
       then have env_tran_right: "env_tran_right \<Gamma> l R" 
         using env_tran env_tran_right_def unfolding env_tran_def by auto
       have concl:"(\<forall>i ns ns'. Suc i<length l \<longrightarrow> 
               \<Gamma>1\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow> 
               snd ((snd c)!(Suc i)) \<notin> Fault ` F  \<longrightarrow> 
               snd ((snd c)!i) = Normal ns \<and> snd ((snd c)!(Suc i)) = Normal ns' \<longrightarrow>              
                 (snd(l!i), snd(l!(Suc i))) \<in> 
                   (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>))"
       proof -
       { fix k ns ns'
         assume a00:"Suc k<length l" and
                a21:"\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))" and
                a22:"snd (l!k) = Normal ns \<and> snd (l!(Suc k)) = Normal ns'"                                                           
         obtain j where before_k_all_evnt:"j\<le>k \<and>  (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<and> (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
           using a00 a21 exist_first_comp_tran cp by blast
         then obtain cj sj csj ssj where pair_j:"(\<Gamma>\<turnstile>\<^sub>c(cj,sj)  \<rightarrow> (csj,ssj)) \<and> cj = fst (l!j) \<and> sj = snd (l!j) \<and> csj = fst (l!(Suc j)) \<and> ssj = snd(l!(Suc j))"
           by fastforce                                   
         have k_basic:"cj = (Cond b c1 c2) \<and> sj \<in> Normal ` (Collect p)" 
           using  pair_j before_k_all_evnt cp env_tran_right a5 assum a00 stability[of p R l 0 j j \<Gamma>]
         by force
         then obtain s' where ss:"sj = Normal s' \<and> s'\<in> (Collect p)" by auto 
         then have ssj_normal_s:"ssj = Normal s'" using before_k_all_evnt k_basic pair_j
           by (metis prod.collapse snd_conv stepc_Normal_elim_cases(6))          
         have "(snd(l!k), snd(l!(Suc k))) \<in> 
                   (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>)"
           using ss a2 unfolding Satis_def         
         proof (cases "k=j")   
           case True          
             have "(G \<and>* tran_True) (s', s')" 
               using ss I_fence_G fence_I_id a2 sep_conj_train_True
               by (metis mem_Collect_eq surjective_pairing)                        
             thus "(snd (l ! k), snd (l ! Suc k)) \<in> (\<lambda>(pa, p). (Normal pa, Normal p)) ` Collect (G \<and>* tran_True)"
               using pair_j k_basic True ss ssj_normal_s by auto
         next
           case False
           have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce 
           have l_suc:"l!(Suc j) = (csj, Normal s')" 
             using before_k_all_evnt pair_j  ssj_normal_s
             by fastforce
           have l_k:"j<k" using  before_k_all_evnt False by fastforce
           have "s'\<in>b \<or> s'\<notin>b" by auto                         
           thus "(snd (l ! k), snd (l ! Suc k)) \<in> (\<lambda>(pa, p). (Normal pa, Normal p)) ` Collect (G \<and>* tran_True)"
           proof
             assume a000:"s'\<in>b"
             then have cj:"csj=c1" using k_basic pair_j ss 
                  by (metis (no_types) fst_conv stepc_Normal_elim_cases(6))
             moreover have p1:"(p and (set_fun b)) s'" using a000 ss by blast 
             moreover then have "cp \<Gamma> csj ssj \<inter> assum((p and (set_fun b)), R) F \<subseteq> comm(G, (q,a)) F"
               using a3 com_validity_def cj by blast             
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
               using l_suc j_length a10 a11 \<Gamma>1  ssj_normal_s
                     cptn_assum_induct[of \<Gamma> l "(LanguageCon.com.Cond b c1 c2)" s p R F "Suc j" c1 s' "(p and (set_fun b))"]
               by blast                         
             show ?thesis 
               using l_k drop_comm a00 a21 a22 a10 \<Gamma>1  
               cptn_comm_induct[of \<Gamma> l "(LanguageCon.com.Cond b c1 c2)" s _ "Suc j" G q a F k ns ns']
               unfolding Satis_def by fastforce                        
           next
             assume a000:"s'\<notin>b"
              then have cj:"csj=c2" using k_basic pair_j ss 
                  by (metis (no_types) fst_conv stepc_Normal_elim_cases(6))
             moreover have p1:"(p and (not (set_fun b))) s'" using a000 ss by fastforce
             moreover then have "cp \<Gamma> csj ssj \<inter> assum((p and (not (set_fun b))), R) F \<subseteq> comm(G, (q,a)) F"
               using a4 com_validity_def cj by blast             
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
               using l_suc j_length a10 a11 \<Gamma>1  ssj_normal_s
                     cptn_assum_induct[of \<Gamma> l "(LanguageCon.com.Cond b c1 c2)" s p R F "Suc j" c2 s' "(p and (not (set_fun b)))"]
               by blast             
             show ?thesis 
             using l_k drop_comm a00 a21 a22 a10 \<Gamma>1  
             cptn_comm_induct[of \<Gamma> l "(LanguageCon.com.Cond b c1 c2)" s _ "Suc j" G q a F k ns ns']
             unfolding Satis_def by fastforce
           qed
         qed 
       } thus ?thesis by (simp add: c_prod cp) qed
       have concr:"(final (last l)  \<longrightarrow> 
                   snd (last l) \<notin> Fault ` F  \<longrightarrow>
                   ((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` (Collect q))) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (Collect a)))"
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
       then have k_basic:"cj = (Cond b c1 c2) \<and> sj \<in> Normal ` (Collect p)" 
         using  pair_j before_k_all_evnt cp env_tran_right a5 assum a00 stability[of p R l 0 j j \<Gamma>]
       by fastforce
       then obtain s' where ss:"sj = Normal s' \<and> s'\<in> (Collect p)" by auto 
       then have ssj_normal_s:"ssj = Normal s'" using before_k_all_evnt k_basic pair_j
         by (metis prod.collapse snd_conv stepc_Normal_elim_cases(6))       
       have l_suc:"l!(Suc j) = (csj, Normal s')" 
           using before_k_all_evnt pair_j  ssj_normal_s
           by fastforce
       have "s'\<in>b \<or> s'\<notin>b" by auto 
       then have "((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` (Collect q))) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (Collect a))"
       proof
         assume a000:"s'\<in>b"
         then have cj:"csj=c1" using k_basic pair_j ss 
                  by (metis (no_types) fst_conv stepc_Normal_elim_cases(6))
         moreover have p1:"(p and (set_fun b)) s'" using a000 ss by blast 
         moreover then have "cp \<Gamma> csj ssj \<inter> assum((p and (set_fun b)), R) F \<subseteq> comm(G, (q,a)) F"
           using a3 com_validity_def cj by blast         
         ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
           using l_suc j_length a10 a11 \<Gamma>1  ssj_normal_s
                 cptn_assum_induct[of \<Gamma> l "(LanguageCon.com.Cond b c1 c2)" s p R F "Suc j" c1 s' "(p and (set_fun b))"]
           by blast                   
         thus ?thesis       
           using j_length drop_comm   a10 \<Gamma>1  cptn_comm_induct[of \<Gamma> l "(LanguageCon.com.Cond b c1 c2)" s _ "Suc j" G q a F "Suc j"] valid not_fault 
           by blast
       next
         assume a000:"s'\<notin>b"
         then have cj:"csj=c2" using k_basic pair_j ss 
                  by (metis (no_types) fst_conv stepc_Normal_elim_cases(6))
         moreover have p1:"(p and (not set_fun b)) s'" using a000 ss by blast 
         moreover then have "cp \<Gamma> csj ssj \<inter> assum((p and (not set_fun b)), R) F \<subseteq> comm(G, (q,a)) F"
           using a4 com_validity_def cj by blast         
         ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
           using l_suc j_length a10 a11 \<Gamma>1  ssj_normal_s
                 cptn_assum_induct[of \<Gamma> l "(LanguageCon.com.Cond b c1 c2)" s p R F "Suc j" c2 s' "(p and (not set_fun b))"]
           by blast                   
         thus ?thesis       
           using j_length drop_comm a10 \<Gamma>1  cptn_comm_induct[of \<Gamma> l "(LanguageCon.com.Cond b c1 c2)" s _ "Suc j" G q a F "Suc j"] valid not_fault 
           by blast
       qed
       } thus ?thesis by auto qed
       note res = conjI [OF concl concr]               
      }              
      thus ?thesis using c_prod unfolding comm_def by auto qed      
    } thus ?thesis by auto qed 
  } thus ?thesis by (simp add: com_validity_def[of \<Gamma>] com_cvalidity_def) 
qed

lemma Call_sound: 
      "f \<in> dom \<Gamma> \<Longrightarrow>
       \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (the (\<Gamma> f)) sat [p, I, R, G, q,a] \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> (the (\<Gamma> f)) sat [p, I, R, G, q,a] \<Longrightarrow>
       \<forall>s t. (p imp I) (s,t) \<Longrightarrow>  
       Sta p (R\<and>*tran_Id) \<Longrightarrow>     
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> (Call f) sat [p, I, R, G, q,a]"
proof -  
  assume
    a0:"f \<in> dom \<Gamma>" and
    a1:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (the (\<Gamma> f)) sat [p, I, R, G, q,a]" and
    a2:"\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> (the (\<Gamma> f)) sat [p, I, R, G, q,a]" and    
    a3: "\<forall>s t. (p imp I) (s,t)" and
    a4: "Sta p (R\<and>*tran_Id)"
  then have orig_rule:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Call f) sat [p, I, R, G, q,a]" 
    using lrghoare.Call[of f \<Gamma> \<Theta> F p I R G q a] by blast   
  then have I_fence_G:
    "(I  \<triangleright> G) \<and> (I \<triangleright> R) 
     \<and> (\<forall>s t. ((p or (q or a)) imp (I\<and>*sep_true)) (s,t))"  
    using satis_wellformed by blast  
  then obtain bdy where a0:"\<Gamma> f = Some bdy" using a0 by auto
  { 
    fix s
    assume all_call:"\<forall>(c,p,I,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, I , R, G, q,a]"
    then have a2:"\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (the (\<Gamma> f)) sat [p, I, R, G, q,a]" 
      using a2 com_cvalidity_def by fastforce  
    then have a2:"\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> bdy sat [p, I, R, G, q,a]" using a0 by fastforce
    have "cp \<Gamma> (Call f)  s \<inter> assum(p, R) F \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cp \<Gamma> (Call f) s" and a11:"c \<in> assum(p, R) F"
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof -       
        have cp:"l!0=((Call f),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
        have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast
        have assum:"snd(l!0) \<in> Normal ` (Collect p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                   (snd(l!i), snd(l!(Suc i))) \<in> 
                     (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (R ** tran_Id) \<rfloor>))" 
       using a11 c_prod unfolding assum_def by simp
       then have env_tran:"env_tran \<Gamma> p l R" using env_tran_def cp by blast
       then have env_tran_right: "env_tran_right \<Gamma> l R" 
         using env_tran env_tran_right_def unfolding env_tran_def by auto
       have concl:"(\<forall>i ns ns'. Suc i<length l \<longrightarrow> 
               \<Gamma>1\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow> 
               snd ((snd c)!(Suc i)) \<notin> Fault ` F  \<longrightarrow> 
               snd ((snd c)!i) = Normal ns \<and> snd ((snd c)!(Suc i)) = Normal ns' \<longrightarrow>              
                 (snd(l!i), snd(l!(Suc i))) \<in> 
                   (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>))"
       proof -
       { fix k ns ns'
         assume a00:"Suc k<length l" and
                a21:"\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))" and
                a22:"snd (l!k) = Normal ns \<and> snd (l!(Suc k)) = Normal ns'"                                        
         obtain j where before_k_all_evnt:"j\<le>k \<and>  (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow> (l!(Suc j))) \<and> (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
           using a00 a21 exist_first_comp_tran cp by blast
         then obtain cj sj csj ssj where pair_j:"(\<Gamma>\<turnstile>\<^sub>c(cj,sj)  \<rightarrow> (csj,ssj)) \<and> cj = fst (l!j) \<and> sj = snd (l!j) \<and> csj = fst (l!(Suc j)) \<and> ssj = snd(l!(Suc j))"
           by fastforce                                             
         have k_basic:"cj = (Call f) \<and> sj \<in> Normal ` (Collect p)" 
           using  pair_j before_k_all_evnt cp env_tran_right a4 assum a00 stability[of p R l 0 j j \<Gamma>]
           by force
         then obtain s' where ss:"sj = Normal s' \<and> s'\<in> (Collect p)" by auto 
         then have ssj_normal_s:"ssj = Normal s'" 
           using before_k_all_evnt k_basic pair_j a0 
           by (metis not_None_eq snd_conv stepc_Normal_elim_cases(9))                     
         have "(snd(l!k), snd(l!(Suc k))) \<in> 
                   (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>)"
           using ss a2 unfolding Satis_def
         proof (cases "k=j")   
           case True                                  
           have "(G \<and>* tran_True) (s', s')" 
             using ss I_fence_G fence_I_id a3 sep_conj_train_True
             by (metis mem_Collect_eq surjective_pairing)
           thus "(snd (l ! k), snd (l ! Suc k)) \<in> (\<lambda>(pa, p). (Normal pa, Normal p)) ` Collect (G \<and>* tran_True)"
             using pair_j k_basic True ss ssj_normal_s by auto
         next
           case False   
           have j_k:"j<k" using  before_k_all_evnt False by fastforce                      
           thus "(snd (l ! k), snd (l ! Suc k)) \<in> (\<lambda>(pa, p). (Normal pa, Normal p)) ` Collect (G \<and>* tran_True)"
           proof -
             have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce
             have cj:"csj=bdy" using k_basic pair_j ss a0
               by (metis fst_conv option.distinct(1) option.sel stepc_Normal_elim_cases(9))                
             moreover have p1:"p s'" using ss by blast 
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
             using a00 a21 a22 a10 \<Gamma>1  j_k j_length
             cptn_comm_induct[of \<Gamma> l "Call f" s _ "Suc j" G q a F k ns ns']
             unfolding Satis_def by fastforce                         
          qed            
       qed 
       } thus ?thesis by (simp add: c_prod cp) qed
       have concr:"(final (last l)  \<longrightarrow> 
                   snd (last l) \<notin> Fault ` F  \<longrightarrow>
                   ((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` (Collect q))) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (Collect a)))"
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
           moreover have "fst (l!0) = Call f" using cp by auto
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
          have "((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` (Collect q))) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (Collect a))"
          proof -
            have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce                                 
            then have k_basic:"cj = (Call f) \<and> sj \<in> Normal ` (Collect p)" 
              using  pair_j before_k_all_evnt cp env_tran_right a4 assum a00 stability[of p R l 0 j j \<Gamma>]
              by force
            then obtain s' where ss:"sj = Normal s' \<and> s'\<in> (Collect p)" by auto 
            then have ssj_normal_s:"ssj = Normal s'" 
              using before_k_all_evnt k_basic pair_j a0 
              by (metis not_None_eq snd_conv stepc_Normal_elim_cases(9))
            have cj:"csj=bdy" using k_basic pair_j ss a0
              by (metis fst_conv option.distinct(1) option.sel stepc_Normal_elim_cases(9))                
            moreover have p1:"p s'" using ss by blast 
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
              using j_length drop_comm a10 \<Gamma>1 cptn_comm_induct[of \<Gamma> l "Call f" s _ "Suc j" G q a F "Suc j"] valid not_fault 
              by blast
           qed
         } thus ?thesis by auto 
         qed
       note res = conjI [OF concl concr]               
       thus ?thesis using c_prod unfolding comm_def by auto qed      
    } thus ?thesis by auto qed 
  } thus ?thesis by (simp add: com_validity_def[of \<Gamma>] com_cvalidity_def) 
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
  then have p1:"p s'" using a0 unfolding cp_def assum_def by fastforce  
  show ?thesis 
  proof -    
    let ?c= "(\<Gamma>,l2)"
    have l:"snd((snd ?c!0)) \<in> Normal ` (Collect p)"
     using p1 drop_k_s a1 normal_s unfolding cp_def by auto
    {fix i
     assume a00:"Suc i<length (snd ?c)" 
     assume a11:"(fst ?c)\<turnstile>\<^sub>c((snd ?c)!i)  \<rightarrow>\<^sub>e ((snd ?c)!(Suc i))"
     have "(snd((snd ?c)!i), snd((snd ?c)!(Suc i))) \<in> 
            (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (R \<and>* tran_Id) \<rfloor>)"
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
  "(Suc k < length l1 \<longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c(l1!k)  \<rightarrow> (l1!(Suc k)) \<longrightarrow> 
       snd (l1!k) = Normal ns \<and> snd (l1!(Suc k)) = Normal ns'\<longrightarrow>
       (snd(l1!k), snd(l1!(Suc k))) \<in> 
          (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G \<and>* tran_True) \<rfloor>)) \<and> 
   (fst (last l1) = (Seq c c2) \<and> final (c, snd (last l1)) \<longrightarrow> 
    snd (last (l1)) \<notin> Fault ` F  \<longrightarrow>
      (fst (last l1) = (Seq Skip c2) \<and> 
        (snd (last  l1) \<in> Normal ` (Collect q)) \<or>
      (fst (last l1) = (Seq Throw c2) \<and> 
        snd (last l1) \<in> Normal ` (Collect a))))
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
  have last_len:"last l1 = l1!((length l1) -1)" 
       using len0 using last_conv_nth by blast
  have a03:"(\<forall>i ns ns'.                 
               Suc i<length (snd (\<Gamma>, l2)) \<longrightarrow> 
               fst (\<Gamma>, l2)\<turnstile>\<^sub>c((snd (\<Gamma>, l2))!i)  \<rightarrow> ((snd (\<Gamma>, l2))!(Suc i)) \<longrightarrow>
               snd ((snd (\<Gamma>, l2))!i) = Normal ns \<and> snd ((snd (\<Gamma>, l2))!(Suc i)) = Normal ns' \<longrightarrow>                               
                 (snd((snd (\<Gamma>, l2))!i), snd((snd (\<Gamma>, l2))!(Suc i))) \<in> 
                    (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G \<and>* tran_True) \<rfloor>)) \<and> 
               (final (last (snd (\<Gamma>, l2)))  \<longrightarrow> 
                snd (last (snd (\<Gamma>, l2))) \<notin> Fault ` F  \<longrightarrow>
                  ((fst (last (snd (\<Gamma>, l2))) = Skip \<and> 
                    snd (last (snd (\<Gamma>, l2))) \<in> Normal ` (Collect q))) \<or>
                  (fst (last (snd (\<Gamma>, l2))) = Throw \<and> 
                    snd (last (snd (\<Gamma>, l2))) \<in> Normal ` (Collect a)))"
  using a1 unfolding comm_def by fastforce
  show ?thesis unfolding comm_def 
  proof -
  { fix k ns ns'
    assume a00:"Suc k < length l1"    
    then have "k \<le> length l1" using a2 by fastforce    
    have a00:"Suc k < length l2" using eq_length a00 by fastforce    
    then have "\<Gamma>\<turnstile>\<^sub>c(l1!k)  \<rightarrow> (l1!(Suc k)) \<longrightarrow> 
       snd (l1!k) = Normal ns \<and> snd (l1!(Suc k)) = Normal ns'\<longrightarrow>
      (snd((snd (\<Gamma>, l1))!k), snd((snd (\<Gamma>, l1))!(Suc k))) \<in> 
                      (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G \<and>* tran_True) \<rfloor>)"
    using  pair_\<Gamma>l1 pair_\<Gamma>l2 a00  a03 a3  eq_length
    by (metis (no_types,lifting) a2 Suc_lessD nth_map snd_lift)
  } note l=this
  {
    assume a00: "fst (last l1) = (Seq c c2) \<and> final (c, snd (last l1))" and
           a01:"snd (last (l1)) \<notin> Fault ` F"
    then have c:"c=Skip \<or> c = Throw"
     unfolding final_def by auto    
    then have fst_last_l2:"fst (last l2) = c"                               
      using  last_len a00 l1_not_empty eq_length len0 a2 last_conv_nth last_lift 
      by fastforce      
    also have last_eq:"snd (last l2) = snd (last l1)"      
      using l2_not_empty a2 last_conv_nth last_len last_snd 
      by fastforce
    ultimately have "final (fst (last l2),snd (last l2))" 
     using a00 by auto
    then have "final (last l2)" by auto
    also have "snd (last (l2)) \<notin> Fault ` F"
       using  last_eq a01 by auto
    ultimately have "(fst (last  l2)) = Skip \<and> 
                    snd (last  l2) \<in> Normal ` (Collect q) \<or>
                  (fst (last l2) = Throw \<and> 
                    snd (last l2) \<in> Normal ` (Collect a))"
    using a03 by auto
    then have "(fst (last l1) = (Seq Skip c2) \<and> 
                    snd (last  l1) \<in> Normal ` (Collect q)) \<or>
                  (fst (last l1) = (Seq Throw c2) \<and> 
                    snd (last l1) \<in> Normal ` (Collect a))"
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
  "(Suc k < length l1 \<longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c(l1!k)  \<rightarrow> (l1!(Suc k)) \<longrightarrow> 
       snd (l1!k) = Normal ns \<and> snd (l1!(Suc k)) = Normal ns'\<longrightarrow>
       (snd(l1!k), snd(l1!(Suc k))) \<in> 
          (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G \<and>* tran_True) \<rfloor>)) \<and> 
   (final (last l1) \<longrightarrow> 
    snd (last (l1)) \<notin> Fault ` F  \<longrightarrow>
      (fst (last l1) = Skip \<and> 
        (snd (last  l1) \<in> Normal ` (Collect r)) \<or>
      (fst (last l1) = Throw \<and> 
        snd (last l1) \<in> Normal ` (Collect a))))
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
  have last_len:"last l1 = l1!((length l1) -1)" 
       using len0 using last_conv_nth by blast
  have a03:"(\<forall>i ns ns'.                 
               Suc i<length (snd (\<Gamma>, l2)) \<longrightarrow> 
               fst (\<Gamma>, l2)\<turnstile>\<^sub>c((snd (\<Gamma>, l2))!i)  \<rightarrow> ((snd (\<Gamma>, l2))!(Suc i)) \<longrightarrow>
               snd ((snd (\<Gamma>, l2))!i) = Normal ns \<and> snd ((snd (\<Gamma>, l2))!(Suc i)) = Normal ns' \<longrightarrow>                               
                 (snd((snd (\<Gamma>, l2))!i), snd((snd (\<Gamma>, l2))!(Suc i))) \<in> 
                    (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G \<and>* tran_True) \<rfloor>)) \<and> 
               (final (last (snd (\<Gamma>, l2)))  \<longrightarrow> 
                snd (last (snd (\<Gamma>, l2))) \<notin> Fault ` F  \<longrightarrow>
                  ((fst (last (snd (\<Gamma>, l2))) = Skip \<and> 
                    snd (last (snd (\<Gamma>, l2))) \<in> Normal ` (Collect q))) \<or>
                  (fst (last (snd (\<Gamma>, l2))) = Throw \<and> 
                    snd (last (snd (\<Gamma>, l2))) \<in> Normal ` (Collect a)))"
  using a1 unfolding comm_def by fastforce
  show ?thesis unfolding comm_def 
  proof -
  { fix k ns ns'
    assume a00:"Suc k < length l1"    
    then have "k \<le> length l1" using a2 by fastforce    
    have a00:"Suc k < length l2" using eq_length a00 by fastforce    
    then have "\<Gamma>\<turnstile>\<^sub>c(l1!k)  \<rightarrow> (l1!(Suc k)) \<longrightarrow> 
       snd (l1!k) = Normal ns \<and> snd (l1!(Suc k)) = Normal ns'\<longrightarrow>
      (snd((snd (\<Gamma>, l1))!k), snd((snd (\<Gamma>, l1))!(Suc k))) \<in> 
                      (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G \<and>* tran_True) \<rfloor>)"
    using  pair_\<Gamma>l1 pair_\<Gamma>l2 a00  a03 a3  eq_length
    by (metis (no_types,lifting) a2 Suc_lessD nth_map snd_lift)
  } note l=this
  {
    assume a00: "final (last l1)" and
           a01:"snd (last (l1)) \<notin> Fault ` F"
    then have c:"fst (last l1)=Skip \<or> fst (last l1) = Throw"
      unfolding final_def by auto 
    moreover have "fst (last l1) = Seq (fst (last l2)) c2" 
      using a2 last_len eq_length
    proof -
      have "last l2 = l2 ! (length l2 - 1)"
        using l2_not_empty last_conv_nth by blast
      then show ?thesis
        by (metis One_nat_def a2 l2_not_empty last_len last_lift)
    qed
    ultimately have False
      by (simp add: LanguageCon.com.distinct(5) LanguageCon.com.simps(82))  
  }
  thus ?thesis using l by auto qed
qed

lemma comm_map:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Seq c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) \<and> (\<Gamma>, l2)\<in> comm(G, (q,a)) F" and
  a2:"l1=map (lift c2) l2" 
shows
  "(\<Gamma>, l1)\<in> comm(G, (r,a)) F"
proof - 
  {fix i ns ns'
   have "(Suc i < length (l1) \<longrightarrow>
        \<Gamma>\<turnstile>\<^sub>c (l1 ! i) \<rightarrow> (l1 ! (Suc i)) \<longrightarrow>
        ((snd (l1! i) = Normal ns) \<and>
        (snd (l1 ! (Suc i)) = Normal ns')) \<longrightarrow>
        (snd (l1 ! i), snd (l1 ! Suc i))
          \<in> (\<lambda>(x, y). (Normal x, Normal y)) `
                         (\<lfloor> (G \<and>* tran_True) \<rfloor>)) \<and>
        (SmallStepCon.final (last l1) \<longrightarrow>
                   snd (last l1) \<notin> Fault ` F \<longrightarrow>
                   fst (last l1) = LanguageCon.com.Skip \<and>
                   snd (last l1) \<in> Normal ` Collect r \<or>
                   fst (last l1) = LanguageCon.com.Throw \<and>
                   snd (last l1) \<in> Normal ` Collect a) "
      using comm_map''[of \<Gamma> l1 c1 c2 s l2 G q a F i ns ns' r] a0 a1 a2 
      by fastforce
   }  then show ?thesis using comm_def unfolding comm_def by force       
qed

lemma Seq_sound1: 
assumes
  a0:"(\<Gamma>,x)\<in>cptn_mod" and
  a1:"x!0 = ((Seq P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"\<not> final (last x)" and
  a4:"env_tran_right \<Gamma> x rely"
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
    have "\<forall>c p. fst (case p of (ca::('b \<times> 'c, 'a, 'd) LanguageCon.com, x::('b \<times> 'c, 'd) xstate) \<Rightarrow> (LanguageCon.com.Seq ca c, x)) = LanguageCon.com.Seq (fst p) c"
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
  a4:"env_tran_right \<Gamma> x rely"
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
      have f1: "env_tran_right \<Gamma> ((C', st') # xsa) rely"
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
  a4:"env_tran_right \<Gamma> x rely"
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
           using f1 CptnComp.hyps(2) CptnComp.prems(4) env_tran_tail zero_throw_all_throw by blast
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

thm stepc_elim_cases_Seq_skip_c2

lemma seq_skip_throw:
 "\<Gamma>\<turnstile>\<^sub>c(Seq c1 c2,s) \<rightarrow> (c2,s)  \<Longrightarrow> c1= Skip \<or> (c1=Throw \<and> (\<exists>s2'. s=Normal s2'))"
apply (rule stepc_elim_cases_Seq_skip_c2)
apply fastforce
apply (auto)+
apply (fastforce intro:redex_not_Seq)+
done


lemma Seq_sound: 
      "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p, I, R, G, q,a] \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p, I, R, G, q,a] \<Longrightarrow>
       \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [q, I, R, G, r,a] \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c2 sat [q, I, R, G, r,a] \<Longrightarrow> 
       \<forall>s t. (a imp I) (s,t) \<and> (q imp I)(s,t) \<Longrightarrow>
       Sta a (R\<and>*tran_Id) \<Longrightarrow> 
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> (Seq c1 c2) sat [p, I, R, G, r,a]"
proof -  
  assume
    a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p, I, R, G, q,a]" and
    a1:"\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p, I, R, G, q,a]" and
    a2:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [q, I, R, G, r,a]" and    
    a3: "\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c2 sat [q, I, R, G, r,a]" and
    a4: "\<forall>s t. (a imp I) (s,t) \<and> (q imp I)(s,t)" and 
    a5: "Sta a (R\<and>*tran_Id)"
  then have orig_rule:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Seq c1 c2) sat [p, I, R, G, r,a]" 
    using lrghoare.Seq[of \<Gamma> \<Theta> F c1 p I R G q a c2 r] by blast   
  then have I_fence_G:
    "(I  \<triangleright> G) \<and> (I \<triangleright> R) 
     \<and> (\<forall>s t. ((p or (r or a)) imp (I\<and>*sep_true)) (s,t))"  
    using satis_wellformed by blast    
  { 
    fix s
    assume all_call:"\<forall>(c,p,I,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, I , R, G, q,a]"
    then have a1:"\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c1 sat [p, I, R, G, q,a]" 
      using a1 com_cvalidity_def by fastforce  
    then have a3: "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c2 sat [q, I, R, G, r,a]"
      using a3 com_cvalidity_def all_call by fastforce 
    have "cp \<Gamma> (Seq c1 c2)  s \<inter> assum(p, R) F \<subseteq> comm(G, (r,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cp \<Gamma> (Seq c1 c2) s" and a11:"c \<in> assum(p, R) F"
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (r,a)) F"         
      proof - 
      {
       have cp:"l!0=((Seq c1 c2),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
       have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast
       have assum:"snd(l!0) \<in> Normal ` (Collect p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                 (snd(l!i), snd(l!(Suc i))) \<in> 
                 (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (R ** tran_Id) \<rfloor>))" 
       using a11 c_prod unfolding assum_def by simp
       then have env_tran:"env_tran \<Gamma> p l R" using env_tran_def cp by blast
       then have env_tran_right: "env_tran_right \<Gamma> l R" 
         using env_tran env_tran_right_def unfolding env_tran_def by auto       
       have ?thesis
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
             then have "False" using no_c2 env_tran_right cp cptn_eq_cptn_mod_set Seq_sound3
               by blast
             thus ?thesis by auto
           next             
             assume asm0:"fst (last l) = LanguageCon.com.Throw \<and> snd (last l) = Normal s'"
             then obtain lc1 s1' ys where cp_lc1:"(\<Gamma>,lc1) \<in> cp \<Gamma> c1 s \<and> l = ((map (lift c2) lc1)@((Throw, Normal s1')#ys))"
               using Seq_sound2 cp cptn_eq_cptn_mod_set env_tran_right no_c2 by blast
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
               using \<Gamma>1 assum_map using assum_map cp_lc1 by blast                          
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
             then have a_normal:"snd (l!?lm_lc1) \<in> Normal ` (Collect a)" 
             proof
               have last_lc1:"fst (last lc1) = Throw \<and> snd (last lc1) = Normal s1'" 
               using last_length l_map lm_lc1 last_m_lc1 last_lc1_suc
               by (metis LanguageCon.com.inject(3) fst_conv snd_conv)  
               have "final (last lc1)" using last_lc1 final_def 
                 by blast
               moreover have "snd (last lc1)\<notin> Fault ` F" 
                 using last_lc1 by fastforce
               ultimately have "(fst (last lc1) = Throw \<and> 
                      snd (last lc1) \<in> Normal ` (Collect a))" 
                 using lc1_comm last_lc1 unfolding comm_def by force
               thus ?thesis  using  l_map last_lc1_suc last_m_lc1 last_length by auto
             qed                                         
             have concl:"(\<forall>i ns ns'. Suc i<length l \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow> 
               snd (l!(Suc i)) \<notin> Fault ` F  \<longrightarrow> 
               snd (l!i) = Normal ns \<and> snd (l!(Suc i)) = Normal ns' \<longrightarrow>              
                 (snd(l!i), snd(l!(Suc i))) \<in> 
                   (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>))"
             proof-
             { fix k ns ns'
               assume a00:"Suc k<length l" and
                a21:"\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))" and
                a20: " snd (l!(Suc k)) \<notin> Fault ` F " and
                a22:"snd (l!k) = Normal ns \<and> snd (l!(Suc k)) = Normal ns'"  
                then have i_m_l:"\<forall>i <?lm_lc1 -1 . l!i = ?m_lc1!i" 
                  using cp_lc1
                proof -
                  have "map (lift c2) lc1 \<noteq> []"
                    by (meson lc1_not_empty list.map_disc_iff)
                  then show ?thesis
                    by (metis (no_types) Suc_diff_1 cp_lc1 le_imp_less_Suc length_greater_0_conv less_or_eq_imp_le nth_append)
                qed 
                have "(snd(l!k), snd(l!(Suc k))) \<in> 
                   (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>)"
                proof (cases "Suc k< ?lm_lc1")
                  case True 
                  then have a11': "\<Gamma>\<turnstile>\<^sub>c(?m_lc1!k)  \<rightarrow> (?m_lc1!(Suc k))" 
                    using a11 i_m_l True
                  proof -
                    have "\<forall>n na. \<not> 0 < n - Suc na \<or> na < n - 1"
                      using diff_Suc_eq_diff_pred zero_less_diff by presburger
                    then show ?thesis
                      by (metis (no_types) Suc_lessI True a21 i_m_l l_map zero_less_diff)
                  qed
                  have a22':"snd (?m_lc1!k) = Normal ns \<and> snd (?m_lc1!(Suc k)) = Normal ns'"
                    using a22 i_m_l True
                    by (simp add:  cp_lc1  lc1_not_empty  nth_append)
                  then have "(snd(?m_lc1!k), snd(?m_lc1!(Suc k))) \<in> 
                     (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>)"
                  using a11' a22' m_lc1_comm True comm_dest1 by blast
                  thus ?thesis using i_m_l by (simp add: a22 a22')  
                next
                  case False 
                  then have "(Suc k=?lm_lc1) \<or> (Suc k>?lm_lc1)" by auto
                  thus ?thesis 
                  proof
                    {assume suck:"(Suc k=?lm_lc1)"
                     then have k:"k=?lm_lc1-1" by auto
                     have G_s1':"(G \<and>* tran_True) (s1', s1')"                
                     proof -
                       have "I s1'"
                         using a4 a_normal lm_lc1 by force
                       then show ?thesis
                         by (meson I_fence_G fence_I_id sep_conj_train_True)
                     qed               
                     then show "(snd (l!k), snd (l!Suc k)) \<in>
                               (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>)"               
                     proof -
                       have "snd (l!Suc k) = Normal s1'" 
                         using lm_lc1 suck by fastforce                                
                       also have "\<exists>p. p \<in> Collect (G \<and>* tran_True) \<and> (case p of (p, pa) \<Rightarrow> (Normal p::('b \<times> 'c, 'd) xstate, Normal pa::('b \<times> 'c, 'd) xstate)) = (Normal s1', Normal s1')"
                         by (meson G_s1' case_prod_conv mem_Collect_eq)
                       ultimately show ?thesis using suck k
                         by (metis (no_types) Satis_def image_iff last_lc1_suc)
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
                        by (metis (no_types) cp fst_conv length_map lm_lc1 only_one_component_tran_j snd_conv)
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
                   snd (last l) \<notin> Fault ` F  \<longrightarrow>
                   ((fst (last l) = Skip \<and> 
                    snd (last l) \<in> Normal ` (Collect r))) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in> Normal ` (Collect a)))" 
             proof -
               have l_t:"fst (last l) = Throw" 
                 using lm_lc1 by (simp add: asm0)
               have "?lm_lc1 \<le> length l -1" using cp_lc1 by fastforce
               also have "\<forall>i. ?lm_lc1 \<le>i \<and> i<(length l -1) \<longrightarrow>  \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))"
                 using lm_lc1 cp_lc1 env_tran_right final_always_env_i
                 proof -
                  { fix nn :: nat
                    { assume "\<exists>p. Suc nn < length l \<and> (Normal s1'::('b \<times> 'c, 'd) xstate) = Normal p"
                      then have "\<not> nn < length l - 1 \<or> \<not> length (map (lift c2) lc1) \<le> nn \<or> \<Gamma>\<turnstile>\<^sub>c l ! nn \<rightarrow>\<^sub>e l ! Suc nn"
                        by (metis (no_types) cp env_tran_right final_always_env_i fst_conv lm_lc1 snd_conv) }
                    then have "\<not> nn < length l - 1 \<or> \<not> length (map (lift c2) lc1) \<le> nn \<or> \<Gamma>\<turnstile>\<^sub>c l ! nn \<rightarrow>\<^sub>e l ! Suc nn"
                      by (simp ) }
                  then show ?thesis
                    by meson
                 qed                 
               ultimately have "snd (l ! (length l - 1)) \<in> Normal ` Collect a"
                 using cp_lc1 a_normal a5 env_tran_right stability[of a R l ?lm_lc1 "(length l) -1" _ \<Gamma>] 
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
           using Seq_sound1 False no_c2 env_tran_right cp cptn_eq_cptn_mod_set 
           by blast 
           then have "((\<Gamma>,lc1) \<in> assum(p, R) F)"  
              using \<Gamma>1  a10 a11 assum_map by blast
           then have "(\<Gamma>, lc1)\<in> comm(G, (q,a)) F" using cp_lc1 a1
             by (meson IntI com_validity_def contra_subsetD)
           then show ?thesis
             using comm_map a10 \<Gamma>1 cp_lc1 by fastforce             
         qed
       next         
         case False 
         then obtain i where a0:"i<length l \<and> fst (l ! i) = c2"
           by blast
         then have "\<exists>m. (m < length l \<and> fst (l ! m) = c2) \<and>
                   (\<forall>i<m. \<not> (i < length l \<and> fst (l ! i) = c2))"   
           using exists_first_occ[of "(\<lambda>i. i<length l  \<and> fst (l ! i) = c2)" i] 
           by blast
         then obtain i where a0:"i<length l \<and> fst (l !i) = c2 \<and>
                                (\<forall>j<i. (fst (l ! j) \<noteq> c2))"
           by fastforce
         then obtain s2 where li:"l!i =(c2,s2)" by (meson eq_fst_iff)
         then obtain lc1 lc2 where cp_lc1:"(\<Gamma>,lc1) \<in> (cp \<Gamma> c1 s) \<and> 
                                 (\<Gamma>,lc2) \<in> (cp \<Gamma> c2 (snd (lc1!(i-1)))) \<and> 
                                 l = (map (lift c2) lc1)@lc2"
           using Seq_sound4 a0 using cp env_tran_right by blast  
         then have length_c1_map:"length lc1 = length (map (lift c2) lc1)" 
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
         then have "\<Gamma>\<turnstile>\<^sub>c(Seq (fst (last lc1)) c2,s2) \<rightarrow> (c2, s2)"
           using last_m_lc1  li by fastforce
         then obtain s2' where 
           last_lc1:"fst (last lc1) = Skip \<or> 
            fst (last lc1) = Throw \<and> (s2 = Normal s2')" 
           using seq_skip_throw by blast
         then have "final (last lc1)" 
           using l_is unfolding final_def by auto
         have concl:
           "(\<forall>i ns ns'. Suc i<length l \<longrightarrow> 
           \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow> 
           snd (l!(Suc i)) \<notin> Fault ` F  \<longrightarrow> 
           snd (l!i) = Normal ns \<and> snd (l!(Suc i)) = Normal ns' \<longrightarrow>              
             (snd(l!i), snd(l!(Suc i))) \<in> 
               (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>))"
         proof-
         { fix k ns ns'
           assume a00:"Suc k<length l" and
            a21:"\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k))" and
            a20: " snd (l!(Suc k)) \<notin> Fault ` F " and
            a22:"snd (l!k) = Normal ns \<and> snd (l!(Suc k)) = Normal ns'"  
            then have i_m_l:"\<forall>j <i . l!j = ?m_lc1!j"             
            proof -
              have "map (lift c2) lc1 \<noteq> []"
                by (meson lc1_not_empty list.map_disc_iff)
              then show ?thesis 
                using cp_lc1 i_map length_c1_map by (fastforce simp:nth_append)              
            qed 
            have "(snd(l!k), snd(l!(Suc k))) \<in> 
               (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>)"
            proof (cases "Suc k< i")
              case True 
              then have a11': "\<Gamma>\<turnstile>\<^sub>c(?m_lc1!k)  \<rightarrow> (?m_lc1!(Suc k))" 
                using a11 i_m_l True
              proof -
                have "\<forall>n na. \<not> 0 < n - Suc na \<or> na < n - 1"
                  using diff_Suc_eq_diff_pred zero_less_diff by presburger
                then show ?thesis using True a21 i_m_l by force                  
              qed
              have a22':"snd (?m_lc1!k) = Normal ns \<and> snd (?m_lc1!(Suc k)) = Normal ns'"
                using a22 i_m_l True
                by (simp add:  cp_lc1  lc1_not_empty  nth_append)
              have "Suc k < length ?m_lc1" using True i_map length_c1_map by metis
              then have "(snd(?m_lc1!k), snd(?m_lc1!(Suc k))) \<in> 
                 (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>)"
              using a11' a22' m_lc1_comm True i_map length_c1_map comm_dest1 
                by blast
              thus ?thesis using i_m_l by (simp add: a22 a22')  
            next
              case False 
              then have "(Suc k=i) \<or> (Suc k>i)" by auto
              thus ?thesis 
              proof
                {assume suck:"(Suc k=i)"
                 then have k:"k=i-1" by auto
                 have G_s1':"(G \<and>* tran_True) (s2', s2')"                
                 proof -
                   have "I s2'"
                     using a4   by force
                   then show ?thesis
                     by (meson I_fence_G fence_I_id sep_conj_train_True)
                 qed               
                 then show "(snd (l!k), snd (l!Suc k)) \<in>
                           (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (G ** tran_True) \<rfloor>)"               
                 proof -
                   have "snd (l!Suc k) = Normal s1'" 
                     using lm_lc1 suck by fastforce                                
                   also have "\<exists>p. p \<in> Collect (G \<and>* tran_True) \<and> (case p of (p, pa) \<Rightarrow> (Normal p::('b \<times> 'c, 'd) xstate, Normal pa::('b \<times> 'c, 'd) xstate)) = (Normal s1', Normal s1')"
                     by (meson G_s1' case_prod_conv mem_Collect_eq)
                   ultimately show ?thesis using suck k
                     by (metis (no_types) Satis_def image_iff last_lc1_suc)
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
                    by (metis (no_types) cp fst_conv length_map lm_lc1 only_one_component_tran_j snd_conv)
                qed
                then have "\<not>(\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow> (l!(Suc k)))"
                  using a00 a001 by auto                    
                then show ?thesis using a21 by fastforce                    
              }
              qed 
            qed
          } thus ?thesis by auto 
         qed 


  
         thus ?thesis sorry
       qed           
     } thus ?thesis by auto qed
   } thus ?thesis by auto qed 
 } thus ?thesis by (simp add: com_validity_def[of \<Gamma>] com_cvalidity_def) 
qed

lemma localRG_sound: "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p, I, R, G, q,a] \<Longrightarrow> \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> c sat [p, I, R, G, q,a]"
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
  case Seq thus ?case sorry
sorry   

end
theory CRef
imports Main "CSimpl.LocalRG_HoareDef" "EmbSimpl.HoareTotalProps"
begin
  
abbreviation \<tau>  where "\<tau> \<equiv> None"
  
definition Id where "Id \<equiv> {(x,y). x = y}"  

  
  
lemma str1:
  assumes a0:"si\<^sub>s < length l\<^sub>s \<and> l\<^sub>s ! si\<^sub>s = (csuci'\<^sub>s, ssuci'\<^sub>s)" 
  shows "\<exists>sis'. sis' < length (l'\<^sub>s@ l\<^sub>s) \<and> (l'\<^sub>s@ l\<^sub>s) ! sis' = (csuci'\<^sub>s, ssuci'\<^sub>s)"          
  using a0 by (induct l'\<^sub>s, auto)
    
lemma str2:
  "j>0 \<Longrightarrow> j< length l \<Longrightarrow>
   \<forall>i<j. ((take j l)@ l')!i = l!i" 
by (simp add: nth_append)

lemma str3:    
  "j\<ge>length l1 \<Longrightarrow>
   j<length (l1@l') \<Longrightarrow>
   (l1 @ l') ! j = l'!(j-length l1)"
  by (simp add: nth_append)

lemma list_conc:"i< length l \<Longrightarrow> 
                 P1 (l!i) \<Longrightarrow> 
                 P \<longrightarrow> j< length l \<and> P2 (l!j) \<and> j\<ge>i \<Longrightarrow>
                 \<exists>i'. i'< length (l1@l) \<and> P1 ((l1@l)!i') \<and>
                 (P \<longrightarrow> (\<exists>j'. j'<length (l1@l) \<and> P2 ((l1@l)!j') \<and>  j'\<ge>i'))"
proof (induct l1)
  case Nil thus ?case by auto
next
  case (Cons el1 l1) 
  then obtain i' j' where step:"i'<length (l1 @ l) \<and> P1 ((l1 @ l) ! i') \<and> 
    (P \<longrightarrow> (j'<length (l1 @ l) \<and> P2 ((l1 @ l) ! j') \<and> i' \<le> j'))" 
    by auto
  {
    assume p:"P"
    then have "Suc i' < length ((el1#l1)@l) \<and> Suc j' < length ((el1#l1)@l) \<and> P1 (((el1#l1)@l)! Suc i') \<and>
               P2 (((el1#l1)@l)!Suc j') \<and> Suc i' \<le> Suc j'"   
      using step p by fastforce
    then have ?case using step p by fastforce
  }    
  also {
    assume "\<not>P"
    then have ?case using step
      by auto    
  }    
  ultimately show ?case by auto
qed
  
  
inductive       
      "stepce"::"[('s,'p,'f,'e) body,'e option,('s,'p,'f,'e) config,('s,'p,'f,'e) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c\<^sub>_ (_ \<rightarrow>/ _)" [81,81,81,81] 100)  
  for \<Gamma>::"('s,'p,'f,'e) body"
where

  Basicc: "\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Basic f e,Normal s) \<rightarrow> (Skip,Normal (f s))"

| Specc: "(s,t) \<in> r \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c\<^sub>e(Spec r e,Normal s) \<rightarrow> (Skip,Normal t)"
| SpecStuckc: "\<forall>t. (s,t) \<notin> r \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c\<^sub>e(Spec r e,Normal s) \<rightarrow> (Skip,Stuck)"

| Guardc: "s\<in>g \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Guard f g c,Normal s) \<rightarrow> (c,Normal s)"
  
| GuardFaultc: "s\<notin>g \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Guard f g c,Normal s) \<rightarrow> (Skip,Fault f)"


| Seqc: "\<Gamma>\<turnstile>\<^sub>c\<^sub>e(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s')
        \<Longrightarrow> 
        \<Gamma>\<turnstile>\<^sub>c\<^sub>e(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Seq c\<^sub>1' c\<^sub>2, s')"
| SeqSkipc: "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Seq Skip c\<^sub>2,s) \<rightarrow> (c\<^sub>2, s)"
| SeqThrowc: "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Seq Throw c\<^sub>2,Normal s) \<rightarrow> (Throw, Normal s)"

| CondTruec:  "s\<in>b \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Cond b c\<^sub>1 c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>1,Normal s)"
| CondFalsec: "s\<notin>b \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Cond b c\<^sub>1 c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s)"

| WhileTruec: "\<lbrakk>s\<in>b\<rbrakk> 
              \<Longrightarrow> 
              \<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(While b c,Normal s) \<rightarrow> (Seq c (While b c),Normal s)"

| WhileFalsec: "\<lbrakk>s\<notin>b\<rbrakk> 
               \<Longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(While b c,Normal s) \<rightarrow> (Skip,Normal s)"


| Awaitc:  "\<lbrakk>s\<in>b; \<Gamma>1=\<Gamma>\<^sub>\<not>\<^sub>a ; \<Gamma>1\<turnstile>\<langle>ca1,Normal s\<rangle> \<Rightarrow> t; 
             \<not>(\<exists>t'. t = Abrupt t')\<rbrakk> \<Longrightarrow> 
            \<Gamma>\<turnstile>\<^sub>c\<^sub>e(Await b ca1 e,Normal s) \<rightarrow> (Skip,t)"

| AwaitAbruptc: "\<lbrakk>s\<in>b; \<Gamma>1=\<Gamma>\<^sub>\<not>\<^sub>a ; \<Gamma>1\<turnstile>\<langle>ca1,Normal s\<rangle> \<Rightarrow> t; 
                  t = Abrupt t'\<rbrakk> \<Longrightarrow> 
                 \<Gamma>\<turnstile>\<^sub>c\<^sub>e(Await b ca1 e,Normal s) \<rightarrow> (Throw,Normal t')"

| Callc: "\<Gamma> p = Some bdy \<Longrightarrow>  bdy\<noteq>Call p \<Longrightarrow>
         \<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Call p,Normal s) \<rightarrow> (bdy,Normal s)"

| CallUndefinedc: "\<Gamma> p=None \<Longrightarrow>
         \<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Call p,Normal s) \<rightarrow> (Skip,Stuck)"

| DynComc: "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(DynCom c,Normal s) \<rightarrow> (c s,Normal s)"

| Catchc: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c\<^sub>e(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s')\<rbrakk>
          \<Longrightarrow>
          \<Gamma>\<turnstile>\<^sub>c\<^sub>e(Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Catch c\<^sub>1' c\<^sub>2,s')"

| CatchThrowc: "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Catch Throw c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s)"
| CatchSkipc: "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Catch Skip c\<^sub>2,s) \<rightarrow> (Skip,s)"

| FaultPropc:  "\<lbrakk>c\<noteq>Skip; redex c = c\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(c,Fault f) \<rightarrow> (Skip,Fault f)"
| StuckPropc:  "\<lbrakk>c\<noteq>Skip; redex c = c\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(c,Stuck) \<rightarrow> (Skip,Stuck)"
| AbruptPropc: "\<lbrakk>c\<noteq>Skip; redex c = c\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(c,Abrupt f) \<rightarrow> (Skip,Abrupt f)"
  
          
  
lemmas stepce_induct = stepce.induct [of _ _ "(c,s)" "(c',s')", split_format (complete), case_names
Basicc Specc SpecStuckc Guardc GuardFaultc Seqc SeqSkipc SeqThrowc CondTruec CondFalsec
WhileTruec WhileFalsec Awaitc AwaitAbruptc Callc CallUndefinedc DynComc Catchc CatchThrowc CatchSkipc
FaultPropc StuckPropc AbruptPropc, induct set]  

inductive_cases stepc_elim_casese:
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Await b c2 e,s) \<rightarrow> (nc,Normal s')"


inductive_cases stepc_elim_cases1:
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Skip,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Guard f g c,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Basic f e,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Spec r e,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Seq c1 c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Cond b c1 c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(While b c,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Await b c2 e,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Call p,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(DynCom c,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Throw,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Catch c1 c2,s) \<rightarrow> u"

inductive_cases stepc_elim_cases:
"\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Basic f e,Normal s) \<rightarrow> (Skip,Normal (f s))"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Spec r e,Normal s) \<rightarrow> (Skip,Normal t)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Spec r e,Normal s) \<rightarrow> (Skip,Stuck)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Guard f g c,Normal s) \<rightarrow> (c,Normal s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Guard f g c,Normal s) \<rightarrow> (Skip,Fault f)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Seq c\<^sub>1' c\<^sub>2, s')"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Seq Skip c\<^sub>2,s) \<rightarrow> (c\<^sub>2, s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Seq Throw c\<^sub>2,Normal s) \<rightarrow> (Throw, Normal s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Cond b c\<^sub>1 c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>1,Normal s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Cond b c\<^sub>1 c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(While b c,Normal s) \<rightarrow> (Seq c (While b c),Normal s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(While b c,Normal s) \<rightarrow> (Skip,Normal s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Await b ca1 e,Normal s) \<rightarrow> (Skip,t)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Await b ca1 e,Normal s) \<rightarrow> (Throw,Normal t')"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Call p,Normal s) \<rightarrow> (bdy,Normal s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Call p,Normal s) \<rightarrow> (Skip,Stuck)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(DynCom c,Normal s) \<rightarrow> (c s,Normal s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Catch c\<^sub>1' c\<^sub>2,s')"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Catch Throw c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Catch Skip c\<^sub>2,s) \<rightarrow> (Skip,s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(c,Fault f) \<rightarrow> (Skip,Fault f)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(c,Stuck) \<rightarrow> (Skip,Stuck)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(c,Abrupt f) \<rightarrow> (Skip,Abrupt f)"

 
inductive_cases ev_stepc_elim_cases:
  "\<Gamma>\<turnstile>\<^sub>c\<^sub>Some v(c,s) \<rightarrow> u"
  
inductive_cases ev_stepc_normal_elim_cases:
  "\<Gamma>\<turnstile>\<^sub>c\<^sub>Some v(c,Normal s) \<rightarrow> u"

inductive_cases stepc_elim_casestau:
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Skip,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Guard f g c,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Basic f e,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Spec r e,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Seq c1 c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Cond b c1 c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(While b c,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Await b c2 e,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Call p,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(DynCom c,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Throw,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Catch c1 c2,s) \<rightarrow> u"

lemma stepce_stepc:
  "\<Gamma>\<turnstile>\<^sub>c\<^sub>e (c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c (c,s) \<rightarrow> (c',s')"
proof (induct rule: stepce_induct) 
qed (fastforce intro:stepc.intros)+
  
lemma stepc_stepce:
  "\<Gamma>\<turnstile>\<^sub>c (c,s) \<rightarrow> (c',s') \<Longrightarrow>  \<exists>e. \<Gamma>\<turnstile>\<^sub>c\<^sub>e (c,s) \<rightarrow> (c',s')"
proof (induct rule: stepc_induct)  
qed(fastforce intro:stepce.intros)+
  
lemma stepc_stepce_unique:
  "\<Gamma>\<turnstile>\<^sub>c (c,s) \<rightarrow> (c',s') \<Longrightarrow>  \<exists>!e. \<Gamma>\<turnstile>\<^sub>c\<^sub>e (c,s) \<rightarrow> (c',s')"
proof (induct rule: stepc_induct)
qed (fastforce intro: stepce.intros elim: stepc_elim_cases)+
 
inductive_cases stepc_elim_cases_Seq_skip_ev:
  "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Seq Skip c1, \<sigma>) \<rightarrow> u"
  "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Seq Throw c1, \<sigma>) \<rightarrow> u"  
  "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Catch Skip c1, \<sigma>) \<rightarrow> u"
  "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Catch Throw c1, \<sigma>) \<rightarrow> u"  
  
inductive_cases stepc_elim_seq_skip:
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Seq Skip c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Seq Throw c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Catch Skip c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Catch Throw c2,s) \<rightarrow> u"
 
inductive_cases evstepc_elim_seq:
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Seq c1 c2,s) \<rightarrow> (Seq c1' c2,s')"  
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Catch c1 c2,s) \<rightarrow> (Catch c1' c2,s')"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow> (c, s')"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow> (c, s')"
  
inductive_cases stepc_elim_cases2:
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Cond b c1 c2,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Guard f b c,Normal s) \<rightarrow> u"
  

lemma dest_while: 
  "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(While b c,Normal s) \<rightarrow> (c1,s') \<Longrightarrow> 
    s' = Normal s \<and> 
    ((s\<in>-b \<and> c1=Skip) \<or> 
    (s\<in>b \<and> c1 = Seq c (LanguageCon.com.While b c)))
    "
  by (fastforce elim:stepc_elim_cases1(7)) 
  
(* lemmas on skip and throw *) 
  
lemma skip1:
  assumes a4:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (LanguageCon.com.Skip, \<sigma>) \<rightarrow> (c1, s1)"
     shows "P"
proof -
  have "\<not>\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (LanguageCon.com.Skip, \<sigma>) \<rightarrow> (c1, s1)"
    using SmallStepCon.stepc_elim_cases(1) stepce_stepc by blast     
  thus ?thesis using a4 by auto
qed
  
lemma throw1:
  assumes a4:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (LanguageCon.com.Throw, Normal s) \<rightarrow> (c1, s1)"
     shows "P"
proof -
  have "\<not>\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (LanguageCon.com.Throw, Normal s) \<rightarrow> (c1, s1)"
    using SmallStepCon.stepc_elim_cases(11) stepce_stepc
    by fastforce      
  thus ?thesis using a4 by auto
qed  
  
lemma catch_ev:
  assumes "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (LanguageCon.com.Throw, \<sigma>') \<rightarrow> (c1, s1)"
  shows "P"
  using assms stepc_elim_cases1(11) by fastforce
  
    
lemma not_catch_skip_throw_ev:
  assumes a4:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Catch Skip c1, \<sigma>) \<rightarrow> (c1', s1) \<or> 
              \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Catch Throw c1, \<sigma>) \<rightarrow> (c1', s1)"
     shows "P"
proof -
  have "\<not>\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Catch Skip c1, \<sigma>) \<rightarrow> (c1', s1)"    
    by (meson stepc_elim_cases1(1) stepc_elim_cases_Seq_skip_ev(3))
  moreover have "\<not>\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Catch Throw c1, \<sigma>) \<rightarrow> (c1', s1)"
    using stepc_elim_cases1(11) stepc_elim_cases_Seq_skip_ev(4)
    by (metis option.distinct(1))    
  ultimately show ?thesis using a4 by auto
qed
  
lemma not_seq_skip_throw_ev:
  assumes a4:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Seq Skip c1, \<sigma>) \<rightarrow> (c1', s1) \<or> 
              \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Seq Throw c1, \<sigma>) \<rightarrow> (c1', s1)"
     shows "P"
proof -
  have "\<not>\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Seq Skip c1, \<sigma>) \<rightarrow> (c1', s1)"    
    by (meson stepc_elim_cases1(1) stepc_elim_cases_Seq_skip_ev(1))
  moreover have "\<not>\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Seq Throw c1, \<sigma>) \<rightarrow> (c1', s1)"
    using stepc_elim_cases1(11) stepc_elim_cases_Seq_skip_ev(2)
    by (metis option.distinct(1))    
  ultimately show ?thesis using a4 by auto
qed
  
lemma not_normal_not_event:
  assumes a0:"\<forall>ns. \<sigma> \<noteq> Normal ns" and
              a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (c\<^sub>c, \<sigma>) \<rightarrow> (c1, s1)"
  shows "P"
using a0 a1
proof(induct c\<^sub>c  arbitrary: \<sigma> s1 c1 v)
  case Skip
  then show ?case using ev_stepc_elim_cases by fastforce
next
  case (Basic x1 x2)
  then show ?case using ev_stepc_elim_cases[OF Basic(2)] by fastforce
next
  case (Spec x1 x2)
  then show ?case  using ev_stepc_elim_cases[OF Spec(2)] by fastforce
next
  case (Seq c\<^sub>c1 c\<^sub>c2)
  then show ?case using ev_stepc_elim_cases[OF Seq(4)]
      apply auto by metis    
next
  case (Cond x1 c\<^sub>c1 c\<^sub>c2)
  then show ?case using ev_stepc_elim_cases[OF Cond(4)] by auto
next
  case (While x1 c\<^sub>c)
  then show ?case using ev_stepc_elim_cases[OF While(3)] by auto
next
  case (Call x)
  then show ?case using ev_stepc_elim_cases[OF Call(2)] by auto
next
  case (DynCom x)
  then show ?case using ev_stepc_elim_cases[OF DynCom(3)] by auto
next
  case (Guard x1 x2 c\<^sub>c)
  then show ?case using ev_stepc_elim_cases[OF Guard(3)] by auto
next
  case Throw
  then show ?case using ev_stepc_elim_cases[OF Throw(2)] by auto
next
  case (Catch c\<^sub>c1 c\<^sub>c2)
  then show ?case using ev_stepc_elim_cases[OF Catch(4)] 
      apply auto by metis      
next
  case (Await x1 x2 x3)
  then show ?case using ev_stepc_elim_cases[OF Await(2)] by auto
qed


lemma no_step_skip:"\<not> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (Skip,\<sigma>) \<rightarrow> (c\<^sub>c',\<sigma>')"  
  by (metis stepc_elim_cases1(1))


lemma step_no_skip_no_normal: 
  assumes a0:"c\<noteq> Skip" and a1:"\<forall>\<sigma>n. \<sigma>\<noteq>Normal \<sigma>n"              
  shows "\<exists>\<sigma>' c\<^sub>c'. \<Gamma>\<^sub>c\<turnstile>\<^sub>c (c,\<sigma>) \<rightarrow> (c\<^sub>c',\<sigma>')"
  using a0 a1
proof (induct c)
  case Skip then show ?case by auto 
next
  case (Seq c1 c2)
  then show ?case
    using stepc.SeqSkipc stepc.Seqc by blast   
next
  case (Catch c1 c2)
  then show ?case
    using stepc.CatchSkipc stepc.Catchc by blast
qed(cases \<sigma>;
   metis Basic SmallStepCon.redex.simps stepc.AbruptPropc  stepc.FaultPropc  stepc.StuckPropc)+

lemma stepe_no_skip_no_normal: 
  assumes a0:"c\<noteq> Skip" and a1:"\<forall>\<sigma>n. \<sigma>\<noteq>Normal \<sigma>n"              
  shows "\<exists>\<sigma>' c\<^sub>c' e. \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c,\<sigma>) \<rightarrow> (c\<^sub>c',\<sigma>')"
  using step_no_skip_no_normal[OF a0 a1] stepc_stepce_unique by blast
  
abbreviation 
 "stepce_rtrancl" :: "[('s,'p,'f,'e) body,'e option,('s,'p,'f,'e) config,('s,'p,'f,'e) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c\<^sub>_ (_ \<rightarrow>\<^sup>*/ _)" [81,81,81,81] 100)
 where                                
  "\<Gamma>\<turnstile>\<^sub>c\<^sub>e cf0 \<rightarrow>\<^sup>* cf1 \<equiv> ((CONST stepce \<Gamma> e))\<^sup>*\<^sup>*  cf0 cf1" 
  
abbreviation 
 "stepce_tau_rtrancl" :: "[('s,'p,'f,'e) body,('s,'p,'f,'e) config,('s,'p,'f,'e) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sub>\<tau>\<^sup>*/ _)" [81,81,81] 100)
where                                
  "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sub>\<tau>\<^sup>* cf1 \<equiv> ((CONST stepce \<Gamma> None))\<^sup>*\<^sup>*  cf0 cf1"
  
  abbreviation 
 "stepce_ev_rtrancl" :: "[('s,'p,'f,'e) body,'e, ('s,'p,'f,'e) config,('s,'p,'f,'e) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c\<^sub>_ (_ \<rightarrow>\<^sup>+/ _)" [81,81,81,81] 100)
where                                
  "\<Gamma>\<turnstile>\<^sub>c\<^sub>e cf0 \<rightarrow>\<^sup>+ cf1 \<equiv> \<exists>cf' cf''. \<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sub>\<tau>\<^sup>* cf' \<and>  
                               (\<exists>a. a = Some e \<and> \<Gamma>\<turnstile>\<^sub>c\<^sub>a cf' \<rightarrow> cf'') \<and> 
                                \<Gamma>\<turnstile>\<^sub>c cf'' \<rightarrow>\<^sub>\<tau>\<^sup>* cf1"
  
abbreviation 
 "step_e_rtrancl" :: "[('s,'p,'f,'e) body,('s,'p,'f,'e) config,('s,'p,'f,'e) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sub>e\<^sup>*/ _)" [81,81,81] 100)
where                                
  "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sub>e\<^sup>* cf1 \<equiv> ((CONST step_e \<Gamma>))\<^sup>*\<^sup>*  cf0 cf1"
  (* "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sup>* cf1 \<equiv> (CONST ((stepc \<Gamma>) \<union> (step_e \<Gamma>)))\<^sup>*\<^sup>* cf0 cf1" *)


 lemma catch_ev_s:
  "\<Gamma>\<turnstile>\<^sub>c\<^sub>e (c,s) \<rightarrow>\<^sup>* (c',s') \<Longrightarrow>
  \<Gamma>\<turnstile>\<^sub>c\<^sub>e (Catch c c2,s) \<rightarrow>\<^sup>* (Catch c' c2,s')"
   apply (induct rule: rtranclp_induct2[case_names Refl Step])   
   by ( auto, meson rtranclp.simps stepce.Catchc)  
  
 lemma catch_ev_plus:
  "\<Gamma>\<turnstile>\<^sub>c\<^sub>v (c1, s) \<rightarrow>\<^sup>+ (c1', s') \<Longrightarrow>
  \<Gamma>\<turnstile>\<^sub>c\<^sub>v (LanguageCon.com.Catch c1 c2, s) \<rightarrow>\<^sup>+ (LanguageCon.com.Catch c1' c2 ,s')
"
  using catch_ev_s[of \<Gamma> \<tau> c1 s _ _ c2 ] catch_ev_s[of \<Gamma> \<tau> _ _ c1' s']  
         stepce.Catchc  
  by fastforce    
     
 lemma seq_ev_s:
  "\<Gamma>\<turnstile>\<^sub>c\<^sub>e (c,s) \<rightarrow>\<^sup>* (c',s') \<Longrightarrow>
  \<Gamma>\<turnstile>\<^sub>c\<^sub>e (Seq c c2,s) \<rightarrow>\<^sup>* (Seq c' c2,s')"
   apply (induct rule: rtranclp_induct2[case_names Refl Step])   
   by ( auto, meson rtranclp.simps stepce.Seqc)

lemma seq_ev_plus:
  "\<Gamma>\<turnstile>\<^sub>c\<^sub>v (c1, s) \<rightarrow>\<^sup>+ (c1', s') \<Longrightarrow>
  \<Gamma>\<turnstile>\<^sub>c\<^sub>v (LanguageCon.com.Seq c1 c2, s) \<rightarrow>\<^sup>+ (LanguageCon.com.Seq c1' c2 ,s')
"
  using seq_ev_s[of \<Gamma> \<tau> c1 s _ _ c2 ] seq_ev_s[of \<Gamma> \<tau> _ _ c1' s']  
         stepce.Seqc  
  by fastforce
lemma tran_tau_closure:"\<Gamma>\<turnstile>\<^sub>c (C, \<sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (C', \<sigma>') \<Longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c (C', \<sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (C'', \<sigma>'') \<Longrightarrow>
      \<Gamma>\<turnstile>\<^sub>c (C, \<sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (C'', \<sigma>'')"
  by auto

lemma event_tran_closure_tau_closure:"\<Gamma>\<turnstile>\<^sub>c (C'', \<sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>* (C, \<sigma>) \<Longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c\<^sub>v (C, \<sigma>) \<rightarrow>\<^sup>+  (C', \<sigma>') \<Longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c\<^sub>v (C'', \<sigma>'') \<rightarrow>\<^sup>+  (C', \<sigma>')"
  using tran_tau_closure by fastforce

lemma event_tran_closure_tau_tran:"
      \<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau> (C'', \<sigma>'') \<rightarrow> (C, \<sigma>) \<Longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c\<^sub>v (C, \<sigma>) \<rightarrow>\<^sup>+  (C', \<sigma>') \<Longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c\<^sub>v (C'', \<sigma>'') \<rightarrow>\<^sup>+  (C', \<sigma>')"
  using event_tran_closure_tau_closure
  by (meson converse_rtranclp_into_rtranclp)
        
    lemma step_tau_skip:"\<forall>ns. s \<noteq> Normal ns \<Longrightarrow>
       \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, s)"
proof (induct c)
  case Skip
  then show ?case by auto
next
  case (Seq c1 c2)
  then have f1: "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (c1, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, s)"
  by fastforce
  have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (c2, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, s)"
    using Seq by fastforce
  then show ?case
    using f1 by (meson r_into_rtranclp rtranclp_trans seq_ev_s stepce.SeqSkipc) 
next
  case (Catch c1 c2)  
  then have f1: "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (c1, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, s)"
    by fastforce
  have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (c2, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, s)"
    using Catch by fastforce
  then show ?case  
    by (meson catch_ev_s f1 r_into_rtranclp rtranclp_trans stepce.CatchSkipc)    
next  
qed (metis  FaultPropc StuckPropc AbruptPropc LanguageCon.com.distinct SmallStepCon.redex.simps
              r_into_rtranclp xstate.exhaust)+

lemma step_NotNormal:"\<forall>ns. s \<noteq> Normal ns \<Longrightarrow>
       \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>e (c, s) \<rightarrow> (c', s') \<Longrightarrow>
       s=s'"
  using step_not_normal_s_eq_t stepce_stepc by blast
  
    
lemma tr_step_NotNormal:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c', s') \<Longrightarrow>
        \<forall>ns. s \<noteq> Normal ns \<Longrightarrow>
       s=s'"
proof (induct rule: rtranclp_induct2[case_names Refl Step])
  case Refl
  then show ?case by auto
next
  case (Step c' s' c'' s'')
  then show ?case using step_NotNormal by auto
qed
  
  
inductive       
"step_pev"::"[('s,'p,'f,'e) body, 'e option, ('s,'p,'f,'e) par_config, 
            ('s,'p,'f,'e) par_config] \<Rightarrow> bool"
("_\<turnstile>\<^sub>p\<^sub>_ (_ \<rightarrow>/ _)" [81,81,81] 100)  
where
 ParCompe: "\<lbrakk>i<length Ps;  \<Gamma>\<turnstile>\<^sub>c\<^sub>e(Ps!i,s) \<rightarrow> (r,s')\<rbrakk> \<Longrightarrow>  
           \<Gamma>\<turnstile>\<^sub>p\<^sub>e(Ps, s) \<rightarrow> (Ps[i:=r], s')"
 
 lemmas steppev_induct = step_pev.induct [of _ _ "(c,s)" "(c',s')", split_format (complete), case_names
ParComp, induct set]

inductive_cases step_pev_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>p\<^sub>e(Ps, s) \<rightarrow> u"

inductive_cases step_pev_pair_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>p\<^sub>e(Ps, s) \<rightarrow> (Qs, t)"

inductive_cases step_pev_Normal_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>p\<^sub>e(Ps, Normal s) \<rightarrow> u"
 

 lemma steppe_stepp:
  "\<Gamma>\<turnstile>\<^sub>p\<^sub>e (c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p (c,s) \<rightarrow> (c',s')"  
 proof (induct rule: steppev_induct)    
qed (fastforce intro:step_p.intros stepce_stepc)
  
lemma stepp_steppe:
  "\<Gamma>\<turnstile>\<^sub>p (c,s) \<rightarrow> (c',s') \<Longrightarrow>  \<exists>e. \<Gamma>\<turnstile>\<^sub>p\<^sub>e (c,s) \<rightarrow> (c',s')"
proof (induct rule: steppe_induct)
qed (fastforce dest:stepc_stepce intro: step_pev.intros)
  
  
lemma stepp_steppe_unique:
  "\<Gamma>\<turnstile>\<^sub>p (c,s) \<rightarrow> (c',s') \<Longrightarrow>  \<exists>!e. \<Gamma>\<turnstile>\<^sub>p\<^sub>e (c,s) \<rightarrow> (c',s')"
proof (induct rule: steppe_induct)
  case (ParComp i Ps \<Gamma> s r s')  
  then obtain e where "\<Gamma>\<turnstile>\<^sub>c\<^sub>e (Ps ! i, s) \<rightarrow> (r, s') \<and> (\<forall>f. e\<noteq>f \<longrightarrow> \<not> \<Gamma>\<turnstile>\<^sub>c\<^sub>f (Ps ! i, s) \<rightarrow> (r, s'))"
    using stepc_stepce_unique by fast
  then show ?case using ParComp step_pev_pair_elim_cases step_pev.intros
    by (smt nth_list_update_eq nth_list_update_neq step_change_p_or_eq_s)
qed

  abbreviation 
 "steppev_rtrancl" :: "[('s,'p,'f,'e) body,'e option,('s,'p,'f,'e) par_config,('s,'p,'f,'e) par_config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>p\<^sub>_ (_ \<rightarrow>\<^sup>*/ _)" [81,81,81,81] 100)
 where                                
  "\<Gamma>\<turnstile>\<^sub>p\<^sub>e cf0 \<rightarrow>\<^sup>* cf1 \<equiv> ((CONST step_pev \<Gamma> e))\<^sup>*\<^sup>*  cf0 cf1" 
  
abbreviation 
 "steppev_tau_rtrancl" :: "[('s,'p,'f,'e) body,('s,'p,'f,'e) par_config,('s,'p,'f,'e) par_config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>p (_ \<rightarrow>\<^sub>\<tau>\<^sup>*/ _)" [81,81,81] 100)
where                                
  "\<Gamma>\<turnstile>\<^sub>p cf0 \<rightarrow>\<^sub>\<tau>\<^sup>* cf1 \<equiv> ((CONST step_pev \<Gamma> None))\<^sup>*\<^sup>*  cf0 cf1"
  
  abbreviation 
 "steppeev_ev_rtrancl" :: "[('s,'p,'f,'e) body,'e, ('s,'p,'f,'e) par_config,('s,'p,'f,'e) par_config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>p\<^sub>_ (_ \<rightarrow>\<^sup>+/ _)" [81,81,81,81] 100)
where                                
  "\<Gamma>\<turnstile>\<^sub>p\<^sub>e cf0 \<rightarrow>\<^sup>+ cf1 \<equiv> \<exists>cf' cf''. \<Gamma>\<turnstile>\<^sub>p cf0 \<rightarrow>\<^sub>\<tau>\<^sup>* cf' \<and>  
                               (\<exists>a. a = Some e \<and> \<Gamma>\<turnstile>\<^sub>p\<^sub>a cf' \<rightarrow> cf'') \<and> 
                                \<Gamma>\<turnstile>\<^sub>p cf'' \<rightarrow>\<^sub>\<tau>\<^sup>* cf1"
  

abbreviation 
 "step_pe_rtrancl" :: "[('s,'p,'f,'e) body,('s,'p,'f,'e) par_config,('s,'p,'f,'e) par_config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>p (_ \<rightarrow>\<^sub>e\<^sup>*/ _)" [81,81,81] 100)
where                                
  "\<Gamma>\<turnstile>\<^sub>p cf0 \<rightarrow>\<^sub>e\<^sup>* cf1 \<equiv> ((CONST step_pe \<Gamma>))\<^sup>*\<^sup>*  cf0 cf1"

abbreviation 
 "step_pe_trancl" :: "[('s,'p,'f,'e) body,('s,'p,'f,'e) par_config,('s,'p,'f,'e) par_config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>p (_ \<rightarrow>\<^sub>e\<^sup>+/ _)" [81,81,81] 100)
where                                
  "\<Gamma>\<turnstile>\<^sub>p cf0 \<rightarrow>\<^sub>e\<^sup>+ cf1 \<equiv> ((CONST step_pe \<Gamma>))\<^sup>+\<^sup>+  cf0 cf1"

lemma rtran_eq_tran: "snd cf0 = Normal sn \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p cf0 \<rightarrow>\<^sub>e\<^sup>* cf1 = \<Gamma>\<turnstile>\<^sub>p cf0 \<rightarrow>\<^sub>e\<^sup>+ cf1"
  using ParEnv apply auto
proof -
  assume a1: "snd cf0 = Normal sn"
  assume a2: "\<Gamma>\<turnstile>\<^sub>p cf0 \<rightarrow>\<^sub>e\<^sup>* cf1"
  have "(fst cf0, Normal sn) = cf0"
    using a1 by (metis (full_types) prod.exhaust_sel)
  then show "\<Gamma>\<turnstile>\<^sub>p cf0 \<rightarrow>\<^sub>e\<^sup>+ cf1"
    using a2 by (metis (no_types) rtranclpD step_pe.intros tranclp.r_into_trancl)
qed

 lemma step_p_tau_not_normal:"
       \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>e (c, s) \<rightarrow> (c', s') \<Longrightarrow>
       \<forall>ns. s \<noteq> Normal ns \<Longrightarrow>          
       s=s'"  
using step_NotNormal
proof -
  assume a1: "\<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>e (c, s) \<rightarrow> (c', s')"
  assume "\<forall>ns. s \<noteq> Normal ns"
  then show ?thesis
    using a1 by (meson step_NotNormal step_pev_pair_elim_cases)
qed
  
  
lemma step_p_tau_skip:"
       \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c', s') \<Longrightarrow>
       \<forall>ns. s \<noteq> Normal ns \<Longrightarrow>         
       s=s'"
proof (induct rule: rtranclp_induct2[case_names Refl Step])
  case Refl
  then show ?case by auto
next
  case (Step c' s' c'' s'')
  then show ?case using step_p_tau_not_normal by auto
qed
  
lemma par_tran_comp:"\<Gamma>\<turnstile>\<^sub>p\<^sub>e (as, s) \<rightarrow> (as', s') \<Longrightarrow> 
       \<Gamma>\<turnstile>\<^sub>p\<^sub>e (a#as, s) \<rightarrow> (a#as', s')"
proof-
  assume a0:"\<Gamma>\<turnstile>\<^sub>p\<^sub>e (as, s) \<rightarrow> (as', s')"
  then obtain i r where cond:"i<length as \<and> \<Gamma>\<turnstile>\<^sub>c\<^sub>e(as!i,s) \<rightarrow> (r,s') \<and> as' = as[i:=r]"
    using step_pev_pair_elim_cases[OF a0] by fastforce
  then show ?thesis using ParCompe[of "i+1" "a#as"] by auto
qed

thm converse_rtranclp_induct
lemma par_tran_comp_rtran:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (as', s') \<Longrightarrow>
       \<Gamma>\<^sub>s\<turnstile>\<^sub>p (a#as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (a#as', s')"
proof (induct rule: rtranclp_induct2[case_names Refl Step])
  case Refl
  then show ?case by auto
next
  case (Step as1 s' as1' s'')
  then show ?case using par_tran_comp
    by (metis (no_types, lifting) rtranclp.simps)
qed   
  
  lemma mult_step_in_par:
  " \<Gamma>\<turnstile>\<^sub>c (Coms ! i, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c, s') \<Longrightarrow> i< length Coms \<Longrightarrow>
    \<Gamma>\<turnstile>\<^sub>p (Coms, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Coms[i:=c], s')"  
proof (induct rule: rtranclp_induct2[case_names Refl Step]) 
  case (Refl) show ?case by auto
next 
  case (Step c s c' s')
  then have "i < length (Coms[i := c])"
    by (metis length_list_update)
  then have "\<Gamma>\<turnstile>\<^sub>p\<^sub>\<tau> (Coms[i := c], s) \<rightarrow> (Coms[i := c, i := c'], s')"
    using Step by (metis (no_types) ParCompe nth_list_update_eq)
  then show ?case
    using Step by auto
qed
  
lemma mult_step_in_par_ev:
  " \<Gamma>\<turnstile>\<^sub>c\<^sub>v (Coms ! i, s) \<rightarrow>\<^sup>+ (c, s') \<Longrightarrow> i< length Coms \<Longrightarrow>
    \<Gamma>\<turnstile>\<^sub>p\<^sub>v (Coms, s) \<rightarrow>\<^sup>+ (Coms[i:=c], s')" 
  apply auto
  using  mult_step_in_par ParCompe length_list_update list_update_overwrite nth_list_update_eq
  by (metis length_list_update list_update_overwrite nth_list_update_eq) 

  
    
lemma par_all_skip_rtran:
    "\<forall>i<length C. \<Gamma>\<turnstile>\<^sub>c (C!i, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, s) \<Longrightarrow> length C > 0 \<Longrightarrow>
       \<exists>C'. \<Gamma>\<turnstile>\<^sub>p (C,s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C', s) \<and> (\<forall>i<length C'. C' ! i = Skip) \<and> C' \<noteq> []"
proof (induction C )
  case (Nil) thus ?case by auto
next
  case (Cons a as)   
  {assume a0:"as=Nil"    
   then have "\<Gamma>\<turnstile>\<^sub>p (a#as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (a#as[0:=Skip],s)" 
     using  Cons(2) mult_step_in_par by auto
   then have ?case using a0
     by (metis Cons.prems(1) length_Cons length_list_update less_Suc0 list.discI list.size(3) 
               list_update.simps(1) mult_step_in_par nth_list_update_eq) 
  }
  moreover { fix a1 as1
    assume a0:"as=a1#as1"
    then have "\<forall>i<length (as). \<Gamma>\<turnstile>\<^sub>c (as ! i, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, s)" 
      using Cons by auto
    moreover have "0 < length as" using a0 by auto
    ultimately obtain c'' where 
     x:"\<Gamma>\<turnstile>\<^sub>p (as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c'',s) \<and> (\<forall>i<length c''. c'' ! i = LanguageCon.com.Skip) \<and> c'' \<noteq> []"
      using Cons(1) by auto
    then have "\<Gamma>\<turnstile>\<^sub>p (a#as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (a#c'', s)" using par_tran_comp_rtran by auto
    moreover have step_c:"\<Gamma>\<turnstile>\<^sub>c ((a # c'') ! 0, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, s)" using Cons by auto
    ultimately have "\<Gamma>\<turnstile>\<^sub>p (a # as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip#c'', s)" 
      using ParComp[of 0 "a#c''"] rtranclp.simps
    proof -
      have "\<Gamma>\<turnstile>\<^sub>p (a # c'',s) \<rightarrow>\<^sub>\<tau>\<^sup>* ((a # c'')[0 := LanguageCon.com.Skip], s)"
        using step_c mult_step_in_par by blast
      then show ?thesis
        using \<open>\<Gamma>\<turnstile>\<^sub>p (a # as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (a # c'',s)\<close> by fastforce
    qed 
    then have ?case using x
      by (metis (no_types, lifting) length_Cons less_Suc_eq_0_disj list.discI nth_Cons_0 nth_Cons_Suc)  
  }      
  ultimately show ?case
    using list.exhaust by blast
      
qed  
    
lemma par_not_normal_not_event:
  assumes a0:"\<forall>ns. \<sigma> \<noteq> Normal ns" and
              a1:"\<Gamma>\<turnstile>\<^sub>p\<^sub>(Some v) (c, \<sigma>) \<rightarrow> (c', s1)"
  shows "P"
proof-
  obtain i c1 where "\<Gamma>\<turnstile>\<^sub>c\<^sub>(Some v) (c!i, \<sigma>) \<rightarrow> (c1, s1)"
    using a1 step_pev_pair_elim_cases by blast
  thus ?thesis using not_normal_not_event[OF a0] by fastforce    
qed
  
lemma par_step_tau_skip:"\<forall>ns. s \<noteq> Normal ns \<Longrightarrow>
       0<length c \<Longrightarrow>
       \<exists>c'' s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c'', s') \<and> (\<forall>i<length c''. c''!i = Skip) \<and> 0 < length c''"  
proof (induct c arbitrary: s)
  case Nil thus ?case by auto
next
  case (Cons ch ct)
  { assume a00:"ct = Nil"   
    have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (ch, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, s)"
      by (simp add: Cons.prems(1) step_tau_skip)
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (ch # ct, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip #ct, s)"
      using mult_step_in_par
      by (metis Cons.prems(2) list_update_code(2) nth_Cons_0) 
      then have ?case
        using a00 by auto 
  }
  moreover { fix cth ctt
    assume a00:"ct = (Cons cth ctt)"
    then obtain ct' s' where hyp_step:"
       \<Gamma>\<^sub>s\<turnstile>\<^sub>p (ct, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (ct', s') \<and>
       (\<forall>i<length ct'. ct' ! i = LanguageCon.com.Skip) \<and> 0 < length ct'"
      using Cons by fastforce
    moreover have "s=s'" using step_p_tau_skip Cons(2) calculation by auto
    ultimately have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (ch#ct, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (ch#ct', s)"
      by (simp add: par_tran_comp_rtran)
    moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (ch, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, s)"
      by (simp add: Cons.prems(1) step_tau_skip)
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (ch#ct', s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip#ct', s)"
      by (metis length_Cons list_update_code(2) mult_step_in_par nth_Cons_0 zero_less_Suc)
    ultimately have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (ch#ct, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip#ct', s)"  by auto
      
    then have ?case using hyp_step
      by (metis (no_types, lifting) length_Cons less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc)  
  }
  ultimately show ?case
    using id_take_nth_drop by fastforce
qed
  
lemma par_step_tau_skip_s:
 assumes a0:"\<forall>ns. s \<noteq> Normal ns" and
        a1:"c\<noteq>[]" 
      shows "\<exists>c''. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c'', s) \<and> (\<forall>i<length c''. c''!i = Skip) \<and> 0 < length c''" 
        
proof -
  have a1:"0<length c" using a1 by auto
  obtain c'' s' where step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c'', s') \<and> (\<forall>i<length c''. c''!i = Skip) \<and> 0 < length c''"
    using par_step_tau_skip[OF a0 a1] by fastforce
  then have "s' = s" using step_p_tau_skip[OF  _ a0] by auto
  then show ?thesis using step by auto
qed

 
type_synonym ('s,'s1,'f) inv = "(('s,'f) xstate \<times> ('s1,'f) xstate) set"
type_synonym ('s,'f) rel = "(('s,'f) xstate \<times> ('s,'f) xstate) set"
type_synonym ('s,'s1) invs = "('s \<times> 's1) set"


 definition alpha_xstate::"('s,'s1,'f) inv" ("\<alpha>\<^sub>x")
where "alpha_xstate \<equiv> 
  {(s\<^sub>c,s\<^sub>s). ((\<exists>scn. s\<^sub>c = Normal scn) \<longrightarrow> (\<exists> ssn. s\<^sub>s = Normal ssn)) \<and>
           ((\<exists>scn. s\<^sub>c = Abrupt scn) \<longrightarrow> (\<exists>ssn. s\<^sub>s = Abrupt ssn)) \<and>
           (\<forall>f. (s\<^sub>c = Fault f) \<longrightarrow> s\<^sub>s = Fault f) \<and>
           (s\<^sub>c = Stuck \<longrightarrow> s\<^sub>s = Stuck) }"      

definition alpha_xstate'::"('s,'s1,'f) inv" ("1\<alpha>\<^sub>x")
where "alpha_xstate' \<equiv> 
  {(s\<^sub>c,s\<^sub>s). ((\<exists>scn. s\<^sub>c = Abrupt scn) \<longrightarrow> (\<exists>ssn. s\<^sub>s = Abrupt ssn)) \<and>
           (\<forall>f. (s\<^sub>c = Fault f) \<longrightarrow> s\<^sub>s = Fault f) \<and>
           (s\<^sub>c = Stuck \<longrightarrow> s\<^sub>s = Stuck) }" 


  
definition related_transitions::"('s,'f) rel \<Rightarrow> ('s1,'f) rel \<Rightarrow> 
                                 (('s,'s1) invs) \<Rightarrow> (('s,'f) tran \<times> ('s1,'f) tran) set"
 ("'(_, _')\<^sub>_")
where
"related_transitions R R' \<alpha> \<equiv> {((\<sigma>,\<sigma>'),(\<Sigma>,\<Sigma>')). (\<sigma>,\<sigma>')\<in>R \<and> (\<Sigma>,\<Sigma>')\<in>R'  \<and>
                                (\<forall>\<sigma>n \<Sigma>n. \<sigma> = Normal \<sigma>n \<and> \<Sigma> = Normal \<Sigma>n \<longrightarrow>(\<sigma>n,\<Sigma>n)\<in>\<alpha>) \<and> 
                                (\<forall>\<sigma>n' \<Sigma>n'. \<sigma>' = Normal \<sigma>n' \<and> \<Sigma>' = Normal \<Sigma>n' \<longrightarrow> (\<sigma>n',\<Sigma>n')\<in>\<alpha>)}"



lemma related_transition_intro:"(\<sigma>,\<Sigma>) \<in> \<alpha> \<Longrightarrow>
       (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<Longrightarrow>
       (Normal \<sigma>, Normal \<sigma>n') \<in> G\<^sub>c \<Longrightarrow>
       (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s \<Longrightarrow> ((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> "
  unfolding related_transitions_def by auto

lemma related_transition_tran: 
 " (\<sigma>,\<Sigma>)\<in>\<alpha> \<Longrightarrow>
  (Normal \<Sigma>, Normal \<Sigma>') \<in> G\<^sub>s \<Longrightarrow>
  ((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>', Normal \<Sigma>'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow>
  ((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
  unfolding related_transitions_def by auto

lemma Fault_alpha:
  "(Fault f,s\<^sub>s) \<in> \<alpha>\<^sub>x \<Longrightarrow> s\<^sub>s = Fault f" 
 unfolding alpha_xstate_def by auto
    
lemma Normal_alpha:
"(Normal ns,s\<^sub>s) \<in> \<alpha>\<^sub>x \<Longrightarrow> \<exists>sns. s\<^sub>s = Normal sns" 
  unfolding alpha_xstate_def by auto
    
lemma Abrupt_alpha:
"(Abrupt ns,s\<^sub>s) \<in> \<alpha>\<^sub>x \<Longrightarrow> \<exists>sns. s\<^sub>s = Abrupt sns" 
  unfolding alpha_xstate_def by auto

lemma Stuck_alpha:
"(Stuck,s\<^sub>s) \<in> \<alpha>\<^sub>x \<Longrightarrow> s\<^sub>s = Stuck" 
  unfolding alpha_xstate_def by auto    
    
lemma alpha_not_normal:"(s1,s2) \<in> \<alpha>\<^sub>x \<Longrightarrow> \<not> (\<exists>sn. s1 = Normal sn) \<Longrightarrow>  \<not> (\<exists>sn. s2 = Normal sn)" 
  unfolding alpha_xstate_def by (cases s1, auto) 
    
lemma alpha_not_fault:"(s1,s2) \<in> \<alpha>\<^sub>x \<Longrightarrow> \<not> (s1 = Fault F) \<Longrightarrow>  \<not> (s2 = Fault F)" 
  unfolding alpha_xstate_def by (cases s1, auto) 

lemma Normal_alpha2:" (s1,Normal s2) \<in> \<alpha>\<^sub>x \<Longrightarrow> \<exists>sns. s1 = Normal sns"  
  using alpha_not_normal alpha_xstate_def by blast   

lemma alpha_x_assoc:"(s1,s2)\<in>\<alpha>\<^sub>x \<and> (s1,s3)\<in>\<alpha>\<^sub>x \<Longrightarrow> (s2,s3)\<in>\<alpha>\<^sub>x"
  unfolding alpha_xstate_def by (cases s1, auto)

lemma alpha_x_tran:"(s1,s2)\<in>\<alpha>\<^sub>x \<and> (s2,s3)\<in>\<alpha>\<^sub>x \<Longrightarrow> (s1,s3)\<in>\<alpha>\<^sub>x"
  unfolding alpha_xstate_def by auto

lemma rtc_alpha_alpha:
 "(x1, x2)\<in>\<alpha>\<^sub>x\<^sup>* \<Longrightarrow> (x1,x2)\<in>\<alpha>\<^sub>x"
  by (induction rule: rtrancl_induct, auto simp add: alpha_xstate_def )

lemma Fault_alpha':
  "(Fault f,s\<^sub>s) \<in> 1\<alpha>\<^sub>x \<Longrightarrow> s\<^sub>s = Fault f" 
 unfolding alpha_xstate'_def by auto
        
lemma Abrupt_alpha':
"(Abrupt ns,s\<^sub>s) \<in> 1\<alpha>\<^sub>x \<Longrightarrow> \<exists>sns. s\<^sub>s = Abrupt sns" 
  unfolding alpha_xstate'_def by auto

lemma Stuck_alpha':
"(Stuck,s\<^sub>s) \<in> 1\<alpha>\<^sub>x \<Longrightarrow> s\<^sub>s = Stuck" 
  unfolding alpha_xstate'_def by auto    
    
lemma alpha_not_normal1:"(s1,s2) \<in> 1\<alpha>\<^sub>x \<Longrightarrow> \<not> (\<exists>sn. s1 = Normal sn) \<Longrightarrow>  \<not> (\<exists>sn. s2 = Normal sn)" 
  unfolding alpha_xstate'_def by (cases s1, auto) 
    
lemma tran_clos_alpha_eq:"\<alpha>\<^sub>x = \<alpha>\<^sub>x\<^sup>*"  
  using rtc_alpha_alpha by auto

lemma alpha_x_tran_clos:
"R\<subseteq>\<alpha>\<^sub>x \<Longrightarrow> R\<^sup>* \<subseteq> \<alpha>\<^sub>x"  
  using tran_clos_alpha_eq rtrancl_mono by blast  

    
definition rel_nstate::"(('s,'s1,'f) inv \<times> ('s,'s1,'f) inv) set" ("r\<^sub>n")
where "rel_nstate \<equiv> 
  {(r0,r1). ((Stuck,Stuck)\<in>r0) = ((Stuck,Stuck)\<in>r1) \<and>
            (\<forall>a b. ((Abrupt a,Abrupt b)\<in>r0) = ((Abrupt a, Abrupt b)\<in>r1)) \<and>
            (\<forall>f. ((Fault f,Fault f)\<in>r0) = ((Fault f, Fault f)\<in>r1))
            }"    
  
lemma rel_nstate_alpha:
  assumes a0:"(\<alpha>,\<alpha>\<^sub>')\<in>r\<^sub>n" and a1:"\<alpha>\<subseteq>\<alpha>\<^sub>x" and a2:"(s,s')\<in>\<alpha>" and a3:"\<nexists>ns. s=Normal ns" 
  shows "(s,s')\<in>\<alpha>\<^sub>'"    
proof(cases s)
  case (Normal x1)
  then show ?thesis using a3 by auto
next
  case (Abrupt x2)
  then obtain x2' where "s' = Abrupt x2'" using a1 a2 Abrupt_alpha by fastforce   
  then show ?thesis using a0 a2 Abrupt unfolding rel_nstate_def by auto
next
  case (Fault f)
  then have "s' = Fault f" using a1 a2 Fault_alpha by fastforce   
  then show ?thesis using a0 a2 Fault unfolding rel_nstate_def by auto
  
next
  case Stuck
  then have "s' = Stuck" using a1 a2 Stuck_alpha by fastforce
  then show ?thesis using a0 a2 Stuck unfolding rel_nstate_def by auto
qed
 

definition normal_relation_id ("R\<^sub>n")
  where "normal_relation_id \<equiv> {(x,y). (\<exists>nx ny. x=Normal nx \<and> y=Normal ny) }
" 
    
lemma not_tau_event:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c,s) \<rightarrow> (c1,s1) \<Longrightarrow> \<not> (e=Some v \<and> (\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c, s) \<rightarrow> (c1,s1)))"
  using stepc_stepce_unique stepce_stepc by fastforce
    
lemma not_event_tau:"(e=Some v \<and> (\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c, s) \<rightarrow> (c1,s1))) \<Longrightarrow> \<not> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c,s) \<rightarrow> (c1,s1) "
  using stepc_stepce_unique stepce_stepc by fastforce


lemma not_env_comp:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c, s) \<rightarrow> (c1,s1) \<Longrightarrow> \<not> \<Gamma>\<^sub>c\<turnstile>\<^sub>c(c,s) \<rightarrow>\<^sub>e (c1,s1)"
  using env_c_c' step_change_p_or_eq_s stepce_stepc by blast
    
lemma not_local_comp:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c(c,s) \<rightarrow>\<^sub>e (c1,s1) \<Longrightarrow> \<not> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c, s) \<rightarrow> (c1,s1)"
  using env_c_c' step_change_p_or_eq_s stepce_stepc by blast
    
lemma "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c,s) \<rightarrow> (c1,Normal s1) \<Longrightarrow> \<exists>ns. s = Normal ns"
  using step_not_normal_s_eq_t stepce_stepc by blast

(* method solve =
(
match premises in P[thin]:"\<And>a. ?P a"  \<Rightarrow>
  \<open>insert P\<close>
) *)

primrec eq_f ::"('s,'f) xstate \<Rightarrow> ('s1,'f) xstate \<Rightarrow> bool"
where
"eq_f (Fault f) s = (s = Fault f)"
|"eq_f (Normal _) _ = False"
|"eq_f Stuck _ = False"
|"eq_f (Abrupt _) _ = False"


 definition rel_xstate::"('s,'s1) invs \<Rightarrow> ('s,'s1,'f) inv"  ("'r\<^sub>i_" [81] 100)
   where "rel_xstate \<alpha> \<equiv> {(s\<^sub>c,s\<^sub>s). (s\<^sub>c,s\<^sub>s)\<in>\<alpha>\<^sub>x \<and> 
                          (\<forall>scn scs. s\<^sub>c= Normal scn \<and> s\<^sub>s = Normal scs \<longrightarrow> (scn, scs)\<in>\<alpha>)}"

lemma ri_normal_dest: "(\<sigma>,\<Sigma>)\<in> (r\<^sub>i \<alpha>) \<Longrightarrow> \<sigma> = Normal \<sigma>n \<Longrightarrow> \<exists>\<Sigma>n. \<Sigma>=Normal \<Sigma>n \<and> (\<sigma>n,\<Sigma>n)\<in> \<alpha>"
  unfolding rel_xstate_def
  using Normal_alpha by fastforce

lemma ri_dest: "(\<sigma>,\<Sigma>)\<in> (r\<^sub>i \<alpha>) \<Longrightarrow> (\<sigma>,\<Sigma>)\<in>\<alpha>\<^sub>x"
  unfolding rel_xstate_def
  by fastforce

coinductive "RGSim"::"[('s,'p,'f,'e) body,('s,'p,'f,'e) config, ('s,'f) rel, ('s,'f) rel,
                     ('s,'s1) invs,('s,'s1) invs,('s,'s1)  invs,
                     ('s1,'p,'f,'e) body,('s1,'p,'f,'e) config, ('s1,'f) rel, ('s1,'f) rel
                    ] \<Rightarrow> bool " 
("'(_,_,_,_')/ \<succeq>\<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>')/ '(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81,81] 100)
where
  rgsim: "\<lbrakk>(\<sigma>,\<Sigma>)\<in>\<alpha>\<^sub>x \<and> (\<forall>\<sigma>n. \<sigma> = Normal \<sigma>n  \<longrightarrow> (\<exists>\<Sigma>n. \<Sigma> = Normal \<Sigma>n \<and> (\<sigma>n,\<Sigma>n) \<in> \<alpha>));                    
            \<forall>c\<^sub>c' \<sigma>n'. \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c\<^sub>c,\<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow> 
             (\<exists>c\<^sub>s' \<Sigma>n'.  \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
              (\<sigma>n', \<Sigma>n')\<in>\<alpha> \<and> 
              (((\<sigma>,Normal \<sigma>n'),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s));           
            \<forall>v c\<^sub>c' \<sigma>n' e. e=Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow> 
             (\<exists> c\<^sub>s' \<Sigma>n'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s', Normal \<Sigma>n') \<and> 
              (\<sigma>n', \<Sigma>n')\<in>\<alpha> \<and> (((\<sigma>,Normal \<sigma>n'),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>  
                (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s));           
           (\<forall>\<sigma>' \<Sigma>'. (((\<sigma>,\<sigma>'),(\<Sigma>,\<Sigma>')) \<in> (R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> (\<sigma>',\<Sigma>')\<in>\<alpha>\<^sub>x \<longrightarrow> 
               (\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>'),R\<^sub>s,G\<^sub>s));           
            \<forall>\<sigma>n. c\<^sub>c = Skip \<and> \<sigma> = Normal \<sigma>n \<longrightarrow> (\<exists>\<Sigma>n'. (((\<sigma>, \<sigma>),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
              (\<sigma>n, \<Sigma>n')\<in>\<gamma>\<^sub>q \<and> \<gamma>\<^sub>q\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, Normal \<Sigma>n'));           
            \<forall>\<sigma>n. c\<^sub>c = Throw \<and> \<sigma> = Normal \<sigma>n \<longrightarrow> (\<exists>\<Sigma>n'. (((\<sigma>, \<sigma>),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
              (\<sigma>n, \<Sigma>n')\<in>\<gamma>\<^sub>a \<and> \<gamma>\<^sub>a\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, Normal \<Sigma>n'));           
            \<forall>\<sigma>' c\<^sub>c' e. \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c,\<sigma>) \<rightarrow> (c\<^sub>c',\<sigma>') \<and> (\<forall>\<sigma>n. \<sigma>'\<noteq>Normal \<sigma>n) \<longrightarrow> 
              (\<exists>\<Sigma>' c\<^sub>s'. (\<sigma>',\<Sigma>')\<in>\<alpha>\<^sub>x \<and> (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>')  \<or> (\<exists>v. e = Some v \<and>  \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s',\<Sigma>') )) \<and>
                        (\<sigma>, \<sigma>')\<in>G\<^sub>c \<and>
                        (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',  \<Sigma>'),R\<^sub>s,G\<^sub>s));           
            (\<forall>\<sigma>n. \<sigma> \<noteq> Normal \<sigma>n) \<and> c\<^sub>c = Skip \<longrightarrow> 
              (\<exists>\<Sigma>'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, \<Sigma>') \<and> (\<sigma>,\<Sigma>')\<in>\<alpha>\<^sub>x)                       
          \<rbrakk> \<Longrightarrow> (\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)"
    
inductive_cases sim_elim_cases:
  "(\<Gamma>\<^sub>c,(c,s),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c',s'),R\<^sub>s,G\<^sub>s)" 
 
    
inductive_cases sim_elim_cases_c:
  "(\<Gamma>\<^sub>c,(Skip,s),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c',s'),R\<^sub>s,G\<^sub>s)"  
  "(\<Gamma>\<^sub>c,(Throw, Normal s),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c',s'),R\<^sub>s,G\<^sub>s)"        
  
lemma dest_sim_ev_step:
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
    \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<Longrightarrow>
    \<exists> c\<^sub>s' \<Sigma>n'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s', Normal \<Sigma>n') \<and> 
              (\<sigma>n', \<Sigma>n')\<in>\<alpha> \<and> (((\<sigma>,Normal \<sigma>n'),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>  
                (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)"  
  by (erule sim_elim_cases,auto)  

lemma dest_sim_ev_step1:
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
    (\<forall>c\<^sub>c' \<sigma>n' v. \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow>
    (\<exists> c\<^sub>s' \<Sigma>n'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s', Normal \<Sigma>n') \<and> 
              (\<sigma>n', \<Sigma>n')\<in>\<alpha> \<and> (((\<sigma>,Normal \<sigma>n'),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>  
                (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))"  
  by (erule sim_elim_cases,auto)

lemma dest_sim_ev_step_not_normal:
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
    \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>') \<and> (\<forall>\<sigma>n'. \<sigma>' \<noteq> Normal \<sigma>n') \<Longrightarrow>
    (\<exists>\<Sigma>' c\<^sub>s'. (\<sigma>',\<Sigma>')\<in>\<alpha>\<^sub>x \<and> (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>')  \<or> (\<exists>v. e = Some v \<and>  \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s',\<Sigma>') )) \<and>
              (\<sigma>, \<sigma>')\<in>G\<^sub>c \<and>
                        (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',  \<Sigma>'),R\<^sub>s,G\<^sub>s))"
by (erule sim_elim_cases,auto)
  
    
lemma dest_sim_tau_step:
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
    \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<Longrightarrow>
    \<exists>c\<^sub>s' \<Sigma>n'.  \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
              (\<sigma>n', \<Sigma>n')\<in>\<alpha> \<and> 
              (((\<sigma>,Normal \<sigma>n'),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)"
    by (erule sim_elim_cases,auto)
 
lemma dest_sim_env_step:  
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
   (((\<sigma>,\<sigma>'),(\<Sigma>,\<Sigma>')) \<in> (R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> (\<sigma>',\<Sigma>')\<in>\<alpha>\<^sub>x \<Longrightarrow>
   (\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>'),R\<^sub>s,G\<^sub>s)"
    by (erule sim_elim_cases,auto)
  
 lemma dest_sim_alpha:  
 "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
   \<forall>\<sigma>n. \<sigma> = Normal \<sigma>n  \<longrightarrow> (\<exists>\<Sigma>n. \<Sigma> = Normal \<Sigma>n \<and> (\<sigma>n,\<Sigma>n) \<in> \<alpha>)" 
  by (erule sim_elim_cases,auto)
     
lemma sim_alpha:
assumes   
  a0:"(\<Gamma>,(c,Normal s),R,G) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>',(c',Normal s'),R',G')"
shows "(s,s') \<in> \<alpha>" 
proof -
  show ?thesis using a0 sim_elim_cases(1) by blast
qed

lemma dest_sim_alpha_x:
assumes   
  a0:"(\<Gamma>\<^sub>c,(c\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s)"
shows "(\<sigma>,\<Sigma>) \<in> \<alpha>\<^sub>x" 
proof -
  show ?thesis using a0 sim_elim_cases(1) by blast
qed
  
definition "RGSim_pre"::  
  "[('s,'p,'f,'e) body,('s,'p,'f,'e)com, ('s,'f) rel, ('s,'f) rel,
    ('s,'s1)  invs,('s,'s1)  invs,('s,'s1)  invs, ('s,'s1)  invs,
    ('s1,'p,'f,'e) body,('s1,'p,'f,'e) com, ('s1,'f) rel, ('s1,'f) rel] \<Rightarrow> bool " 
  ("'(_,_,_,_')/ \<succeq>\<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>\<rhd>\<^sub>_\<^sub>;\<^sub>_\<^sub>')/ '(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81,81,81] 100)
  where
" (\<Gamma>\<^sub>c,c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c',R\<^sub>s,G\<^sub>s) \<equiv> 
  \<forall>\<sigma> \<Sigma>. (\<sigma>,\<Sigma>)\<in>\<xi> \<longrightarrow> (\<Gamma>\<^sub>c,(c, Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c',Normal \<Sigma>),R\<^sub>s,G\<^sub>s)
"
    
definition ToNorm :: "('s,'s1,'f)  inv \<Rightarrow> ('s\<times>'s1) set"
  ("\<Down>\<^sub>n_" [81] 100)
  where "ToNorm r \<equiv> {(s1,s2). (Normal s1,Normal s2) \<in> r}"
    
 definition ToInv :: "('s,'s1)  invs \<Rightarrow> ('s1\<times>'s) set"
  ("\<Down>\<^sub>i_" [81] 100)
  where "ToInv r \<equiv> {(s2,s1). (s1, s2) \<in> r}"

definition ToExSt :: "('s,'s1) invs \<Rightarrow> ('s,'s1,'f) inv"
("\<Down>\<^sub>x_" [81] 100)
where "ToExSt r \<equiv>{(\<sigma>,\<Sigma>). (\<exists>\<sigma>n \<Sigma>n. \<sigma>=Normal \<sigma>n \<and> \<Sigma> = Normal \<Sigma>n \<and> (\<sigma>n,\<Sigma>n)\<in>r)}"

     
inductive_set cptn\<^sub>e :: "(('s,'p,'f,'e) confs) set"
where
  CptnOne: " (\<Gamma>, [(P,s)]) \<in> cptn\<^sub>e"
| CptnEnv: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow>\<^sub>e (P,t); (\<Gamma>,(P, t)#xs) \<in> cptn\<^sub>e \<rbrakk> \<Longrightarrow>
             (\<Gamma>,(P,s)#(P,t)#xs) \<in> cptn\<^sub>e"
| CptnComp: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c\<^sub>e(P,s) \<rightarrow> (Q,t); (\<Gamma>,(Q, t)#xs) \<in> cptn\<^sub>e \<rbrakk> \<Longrightarrow> 
              (\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptn\<^sub>e"    
  
    
definition cp\<^sub>e :: "('s,'p,'f,'e) body \<Rightarrow> ('s,'p,'f,'e) com \<Rightarrow> 
                  ('s,'f) xstate \<Rightarrow> (('s,'p,'f,'e) confs) set" where
  "cp\<^sub>e \<Gamma> P s \<equiv> {(\<Gamma>1,l). l!0=(P,s) \<and> (\<Gamma>,l) \<in> cptn\<^sub>e \<and> \<Gamma>1=\<Gamma>}"     
  
  
  
  definition comm\<^sub>e :: 
  "(('s,'f) tran) set \<times> 
   ('s set \<times> 's set) \<Rightarrow>
   'f set \<Rightarrow> 
     (('s,'p,'f,'e) confs) set" where
  "comm\<^sub>e \<equiv> \<lambda>(guar, (q,a)) F. 
            {c. snd (last (snd c)) \<notin> Fault ` F  \<longrightarrow> 
                (\<forall>i e. 
                 Suc i<length (snd c) \<longrightarrow> 
                 (fst c)\<turnstile>\<^sub>c\<^sub>e((snd c)!i)  \<rightarrow> ((snd c)!(Suc i)) \<longrightarrow>                                        
                   (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> guar) \<and> 
                 (final (last (snd c))  \<longrightarrow>                   
                    ((fst (last (snd c)) = Skip \<and> 
                      snd (last (snd c)) \<in> Normal ` q)) \<or>
                    (fst (last (snd c)) = Throw \<and> 
                      snd (last (snd c)) \<in> Normal ` a))}"

definition com_validity :: 
  "('s,'p,'f,'e) body \<Rightarrow>  'f set \<Rightarrow> ('s,'p,'f,'e) com \<Rightarrow> 
    's set \<Rightarrow> (('s,'f) tran) set \<Rightarrow>  (('s,'f) tran) set \<Rightarrow>  
    's set \<Rightarrow>  's set \<Rightarrow>  bool" 
    ("_ \<Turnstile>\<^sub>e\<^bsub>'/_\<^esub>/ _ sat [_,_, _, _,_]" [61,60,0,0,0,0,0,0] 45) where
  "\<Gamma> \<Turnstile>\<^sub>e\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a] \<equiv> 
   \<forall>s. cp\<^sub>e \<Gamma> Pr s \<inter> assum(p, R) \<subseteq> comm\<^sub>e(G, (q,a)) F"
  

  
lemma RG_sim_cp\<^sub>e:      
 shows "\<exists>l. (\<Gamma>\<^sub>s,l) \<in> (cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s') \<and> (\<forall>i. Suc i<length l \<longrightarrow>
           \<Gamma>\<^sub>s\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>
           (snd(l!i), snd(l!(Suc i))) \<in>  R\<^sub>s)"
proof - 
  let ?l1 = "[(c\<^sub>s,s')]"
  have "(\<Gamma>\<^sub>s,[(c\<^sub>s,s')])\<in> (cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s')" unfolding cp\<^sub>e_def by (simp add: cptn\<^sub>e.CptnOne)
  also have "(\<forall>i. Suc i<length ?l1 \<longrightarrow>
           \<Gamma>\<^sub>s\<turnstile>\<^sub>c(?l1!i)  \<rightarrow>\<^sub>e (?l1!(Suc i)) \<longrightarrow>
           (snd(?l1!i), snd(?l1!(Suc i))) \<in>  R\<^sub>s)" by auto
  ultimately show ?thesis by auto
qed
    
lemma RG_sim_fst_env_assum1: 
  assumes    
   a0:"s\<^sub>s \<in> Normal ` p\<^sub>s"
 shows "\<exists>l. (\<Gamma>\<^sub>s,l)\<in>cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and> (\<Gamma>\<^sub>s,l) \<in> assum(p\<^sub>s,R\<^sub>s)"
  proof-
  obtain l1 where 
  l1:"(\<Gamma>\<^sub>s,l1)\<in>(cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s)" and
  l2:"(\<forall>i. Suc i<length l1 \<longrightarrow>
        \<Gamma>\<^sub>s\<turnstile>\<^sub>c(l1!i)  \<rightarrow>\<^sub>e (l1!(Suc i)) \<longrightarrow>
     (snd(l1!i), snd(l1!(Suc i))) \<in>  R\<^sub>s)" 
    using RG_sim_cp\<^sub>e[of \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s] by auto
  then have snd_normal: "snd (l1!0) \<in> Normal ` p\<^sub>s" using l1 a0 unfolding cp\<^sub>e_def by auto  
  then show ?thesis using l1 l2 unfolding assum_def by fastforce
qed  




lemma step_guarantee:  
  assumes a0:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n')" and
  a1: " \<forall>c\<^sub>c' \<sigma>n'. \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c\<^sub>c,\<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow> 
             (\<exists>c\<^sub>s' \<Sigma>n'.  \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
              (\<sigma>n', \<Sigma>n')\<in>\<alpha> \<and> 
              (((\<sigma>,Normal \<sigma>n'),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))" and
  a2:" \<forall>v c\<^sub>c' \<sigma>n'. \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow> 
             (\<exists> c\<^sub>s' \<Sigma>n'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s', Normal \<Sigma>n') \<and> 
              (\<sigma>n', \<Sigma>n')\<in>\<alpha> \<and> (((\<sigma>,Normal \<sigma>n'),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>  
                (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))"
shows "\<exists>\<Sigma>n' c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<or> (\<exists>v. e= Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s',Normal \<Sigma>n')))\<and> 
             (\<sigma>n',\<Sigma>n')\<in>\<alpha> \<and> (\<sigma>,Normal \<sigma>n')\<in>G\<^sub>c"
proof -  
  have "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n') \<or>  (\<exists>v. e = Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n'))" 
    using a0 by auto
  thus ?thesis
  proof
     assume "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n')"
     thus ?thesis using a1 unfolding related_transitions_def by fastforce    
   next
     assume "(\<exists>v. e = Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n'))"
     then obtain v where a0: "e=Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n')" by auto
     then have"(\<exists> c\<^sub>s' \<Sigma>n'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s', Normal \<Sigma>n') \<and> 
              (\<sigma>n', \<Sigma>n')\<in>\<alpha> \<and> (((\<sigma>,Normal \<sigma>n'),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>  
                (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))"
       using a2 by auto 
     thus ?thesis using a0 unfolding related_transitions_def by blast
  qed    
qed
  

  
lemma step_sim:
  assumes a0:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n')" and
  a1: " \<forall>c\<^sub>c' \<sigma>n'. \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c\<^sub>c,\<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow> 
             (\<exists>c\<^sub>s' \<Sigma>n'.  \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
              (\<sigma>n', \<Sigma>n')\<in>\<alpha> \<and> 
              (((\<sigma>,Normal \<sigma>n'),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))" and
  a2:" \<forall>v c\<^sub>c' \<sigma>n'. \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow> 
             (\<exists> c\<^sub>s' \<Sigma>n'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s', Normal \<Sigma>n') \<and> 
              (\<sigma>n', \<Sigma>n')\<in>\<alpha> \<and> (((\<sigma>,Normal \<sigma>n'),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>  
                (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))"
  shows "\<exists>c\<^sub>s' \<Sigma>n'. (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s) "
proof -  
  have "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n') \<or>  (\<exists>v. e = Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n'))" 
    using a0 by auto
  thus ?thesis
  proof
     assume "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n')"
     thus ?thesis using a1 by fastforce    
   next
     assume "(\<exists>v. e = Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n'))"     
     thus ?thesis using a2 by fastforce
  qed    
qed

lemma step_sim_not_normal:
  assumes a0:" \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c,\<sigma>) \<rightarrow> (c\<^sub>c',\<sigma>') \<and> (\<forall>\<sigma>n. \<sigma>'\<noteq>Normal \<sigma>n)" and
  a1: " \<forall>\<sigma>' c\<^sub>c' e. \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c,\<sigma>) \<rightarrow> (c\<^sub>c',\<sigma>') \<and> (\<forall>\<sigma>n. \<sigma>'\<noteq>Normal \<sigma>n) \<longrightarrow> 
              (\<exists>\<Sigma>' c\<^sub>s'. (\<sigma>',\<Sigma>')\<in>\<alpha>\<^sub>x \<and> (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>')  \<or> 
                        (\<exists>v. e = Some v \<and>  \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s',\<Sigma>') )) \<and>
                             (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',  \<Sigma>'),R\<^sub>s,G\<^sub>s))"
  shows "\<exists>c\<^sub>s' \<Sigma>'. (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s) "
proof - 
  show ?thesis using a0 a1 by fast
qed
    

     
lemma sim_next_state:
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
   \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n') \<Longrightarrow>
  \<exists>c\<^sub>s' \<Sigma>n'.  \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<or> (\<exists>v. e= Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s', Normal \<Sigma>n')) \<and> 
     (\<sigma>n',\<Sigma>n')\<in>\<alpha> \<and> ((\<sigma>,Normal \<sigma>n)\<in>G\<^sub>c)"
  apply (erule sim_elim_cases, drule step_guarantee)
  apply auto
  by (metis not_normal_not_event)+
    
  
  lemma sim_guarantee_normal:
"(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
 \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n') \<Longrightarrow>
\<exists>c\<^sub>s' \<Sigma>n'. (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)"
    apply (erule sim_elim_cases, drule step_sim)          
    by auto


lemma sim_guarantee_not_normal:  
 "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow> 
 \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c', \<sigma>') \<Longrightarrow> \<forall>\<sigma>n'. \<sigma>' \<noteq> Normal \<sigma>n' \<Longrightarrow>
 \<exists>\<Sigma>' c\<^sub>s'. (\<sigma>',\<Sigma>')\<in>\<alpha>\<^sub>x \<and> (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>')  \<or> (\<exists>v. e = Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s',\<Sigma>') )) \<and> 
       (\<sigma>, \<sigma>')\<in>G\<^sub>c \<and>
          (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)"   
  apply (erule sim_elim_cases)  
  by auto

lemma sim_guarantee:  
 "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow> 
 \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c', \<sigma>') \<Longrightarrow>
 \<exists>\<Sigma>' c\<^sub>s'.  (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',\<Sigma>'),R\<^sub>s,G\<^sub>s)"   
  using sim_guarantee_not_normal sim_guarantee_normal
  by fastforce


 coinductive "RGSIM"::"[('s,'p,'f,'e) body,('s,'p,'f,'e) par_config, ('s,'f) rel, ('s,'f) rel,
                      ('s,'s1) invs,('s,'s1) invs,('s,'s1)  invs,
                     ('s1,'p,'f,'e) body,('s1,'p,'f,'e) par_config, ('s1,'f) rel, ('s1,'f) rel
                    ] \<Rightarrow> bool " 
("'(_,_,_,_')/ \<succeq>\<^sub>p\<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>')/ '(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81,81] 100)
where
  RGSIM: "\<lbrakk>(\<sigma>,\<Sigma>)\<in>\<alpha>\<^sub>x \<and> (\<forall>\<sigma>n. \<sigma> = Normal \<sigma>n  \<longrightarrow> (\<exists>\<Sigma>n. \<Sigma> = Normal \<Sigma>n \<and> (\<sigma>n,\<Sigma>n) \<in> \<alpha>));                    
           \<forall>c\<^sub>c' \<sigma>n'. (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>\<tau> (c\<^sub>c,\<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')) \<longrightarrow> 
             (\<exists>c\<^sub>s' \<Sigma>n'.  \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
              (\<sigma>n', \<Sigma>n')\<in>\<alpha> \<and> 
              (((\<sigma>,Normal \<sigma>n'),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s));           
             \<forall>v c\<^sub>c' \<sigma>n' e. e=Some v \<and> (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')) \<longrightarrow> 
             (\<exists> c\<^sub>s' \<Sigma>n'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s', Normal \<Sigma>n') \<and> 
              (\<sigma>n', \<Sigma>n')\<in>\<alpha> \<and> (((\<sigma>,Normal \<sigma>n'),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>  
                (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s));                      
           (\<forall>\<sigma>' \<Sigma>'. (((\<sigma>,\<sigma>'),(\<Sigma>,\<Sigma>')) \<in> (R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> (\<sigma>',\<Sigma>')\<in>\<alpha>\<^sub>x \<longrightarrow> 
               (\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>'),R\<^sub>s,G\<^sub>s));           
             \<forall>\<sigma>n. \<sigma> = Normal \<sigma>n \<and>  (\<forall>i<length c\<^sub>c. c\<^sub>c!i = Skip) \<and> 0 < length c\<^sub>c \<longrightarrow> 
              (\<exists>\<Sigma>n' c\<^sub>s'. (((\<sigma>, \<sigma>),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                (\<sigma>n, \<Sigma>n')\<in>\<gamma>\<^sub>q \<and> \<gamma>\<^sub>q\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and> 
                (\<forall>i<length c\<^sub>s'. c\<^sub>s'!i = Skip) \<and> 0 < length c\<^sub>s');                   
            \<forall>\<sigma>n. \<sigma> = Normal \<sigma>n \<and> final_c (c\<^sub>c,\<sigma>) \<and> (\<exists>i<length c\<^sub>c. c\<^sub>c!i = Throw) \<longrightarrow> 
              (\<exists>\<Sigma>n' c\<^sub>s'. (((\<sigma>, \<sigma>),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (\<sigma>n, \<Sigma>n')\<in>\<gamma>\<^sub>a \<and> \<gamma>\<^sub>a\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and> 
                final_c (c\<^sub>s',(Normal \<Sigma>n')) \<and> (\<exists>i<length c\<^sub>s'. c\<^sub>s'!i = Throw));                
            \<forall>\<sigma>' c\<^sub>c' e. (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>) \<rightarrow> (c\<^sub>c',\<sigma>')) \<and> (\<forall>\<sigma>n. \<sigma>'\<noteq>Normal \<sigma>n) \<longrightarrow> 
              (\<exists>\<Sigma>' c\<^sub>s'. (\<sigma>',\<Sigma>')\<in>\<alpha>\<^sub>x \<and> 
                        (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>')  \<or> (\<exists>v. e = Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s',\<Sigma>') )) \<and>
                        (\<sigma>, \<sigma>')\<in>G\<^sub>c \<and>
                        (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s));                
            (\<forall>\<sigma>n. \<sigma> \<noteq> Normal \<sigma>n) \<and>  (\<forall>i<length c\<^sub>c. c\<^sub>c!i = Skip) \<and> 0 < length c\<^sub>c \<longrightarrow> 
              (\<exists>\<Sigma>' c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<and> (\<sigma>,\<Sigma>')\<in>\<alpha>\<^sub>x \<and>
                (\<forall>i<length c\<^sub>s'. c\<^sub>s'!i = Skip) \<and> 0 < length c\<^sub>s')       
          \<rbrakk> \<Longrightarrow> (\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)"

inductive_cases par_sim_elim_cases:
  "(\<Gamma>\<^sub>c,(c,s),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c',s'),R\<^sub>s,G\<^sub>s)" 
 
lemma dest_SIM_alpha:  
 "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
   (\<sigma>,\<Sigma>) \<in> \<alpha>\<^sub>x \<and> (\<forall>\<sigma>n. \<sigma> = Normal \<sigma>n  \<longrightarrow> (\<exists>\<Sigma>n. \<Sigma> = Normal \<Sigma>n \<and> (\<sigma>n,\<Sigma>n) \<in> \<alpha>))"
  by (erule par_sim_elim_cases,auto)  

lemma dest_SIM_ev_step:
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
     \<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>(Some v) (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<Longrightarrow>
    \<exists> c\<^sub>s' \<Sigma>n'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s', Normal \<Sigma>n') \<and> 
              (\<sigma>n', \<Sigma>n')\<in>\<alpha> \<and> (((\<sigma>,Normal \<sigma>n'),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>  
                (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)"  
  by (erule par_sim_elim_cases,auto)
    
lemma dest_SIM_tau_step:
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
    \<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>\<tau> (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<Longrightarrow>
   \<exists>c\<^sub>s' \<Sigma>n'.  \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
              (\<sigma>n', \<Sigma>n')\<in>\<alpha> \<and> 
              (((\<sigma>,Normal \<sigma>n'),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)"
  by (erule par_sim_elim_cases,auto)
        
lemma dest_SIM_env_step:  
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
   (((\<sigma>,\<sigma>'),(\<Sigma>,\<Sigma>')) \<in> (R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> (\<sigma>',\<Sigma>')\<in>\<alpha>\<^sub>x \<Longrightarrow>
   (\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>'),R\<^sub>s,G\<^sub>s)"
  by (erule par_sim_elim_cases,auto)
    
 lemma dest_SIM_skip_term:
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
   \<forall>\<sigma>n. \<sigma> = Normal \<sigma>n \<and> (\<forall>i<length c\<^sub>c. c\<^sub>c!i = Skip) \<and> 0 < length c\<^sub>c \<Longrightarrow>
   \<exists>\<Sigma>n' c\<^sub>s'. (((\<sigma>, \<sigma>),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
            (\<sigma>n, \<Sigma>n')\<in>\<gamma>\<^sub>q \<and> \<gamma>\<^sub>q\<subseteq>\<alpha> \<and> 
           \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and> 
            (\<forall>i<length c\<^sub>s'. c\<^sub>s'!i = Skip) \<and> 0 < length c\<^sub>s'"
  by (erule par_sim_elim_cases,auto)
    
 lemma dest_SIM_throw_term:
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
    \<forall>\<sigma>n. \<sigma> = Normal \<sigma>n \<and> final_c (c\<^sub>c,\<sigma>) \<and> (\<exists>i<length c\<^sub>c. c\<^sub>c!i = Throw) \<Longrightarrow>
   \<exists>\<Sigma>n' c\<^sub>s'. (((\<sigma>, \<sigma>),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (\<sigma>n, \<Sigma>n')\<in>\<gamma>\<^sub>a \<and> \<gamma>\<^sub>a\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and> 
                final_c (c\<^sub>s',(Normal \<Sigma>n')) \<and> (\<exists>i<length c\<^sub>s'. c\<^sub>s'!i = Throw)"
   by (erule par_sim_elim_cases, auto)
  
     
 lemma dest_SIM_not_Normal_transition:
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
   \<forall>\<sigma>' c\<^sub>c'. (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>) \<rightarrow> (c\<^sub>c',\<sigma>')) \<and> (\<forall>\<sigma>n. \<sigma>'\<noteq>Normal \<sigma>n) \<Longrightarrow>
   \<exists>\<Sigma>' c\<^sub>s'. (\<sigma>',\<Sigma>')\<in>\<alpha>\<^sub>x \<and> (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>')  \<or> \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c', \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s',\<Sigma>') ) \<and>
            (((\<sigma>, \<sigma>'),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
            (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)"
   by (erule par_sim_elim_cases,auto)
    
definition "RGSIM_p_pre"::  
  "[('s,'p,'f,'e) body,('s,'p,'f,'e)par_Simpl, ('s,'f) rel, ('s,'f) rel,
    ('s,'s1)  invs,('s,'s1)  invs,('s,'s1)  invs, ('s,'s1)  invs,
    ('s1,'p,'f,'e) body,('s1,'p,'f,'e) par_Simpl, ('s1,'f) rel, ('s1,'f) rel] \<Rightarrow> bool " 
  ("'(_,_,_,_')/ \<succeq>\<^sub>p\<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>\<rhd>\<^sub>_\<^sub>;\<^sub>_\<^sub>')/ '(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81,81,81] 100)
  where
" (\<Gamma>\<^sub>c,c\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s) \<equiv> 
  \<forall>\<sigma> \<Sigma>. (\<sigma>,\<Sigma>)\<in>\<xi> \<longrightarrow> (\<Gamma>\<^sub>c,(c\<^sub>c, Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,Normal \<Sigma>),R\<^sub>s,G\<^sub>s)
"

inductive_set par_cptn\<^sub>e :: "(('s,'p,'f,'e) par_confs) set"
  where    
  ParCptnOne: "(\<Gamma>, [(P,s)]) \<in> par_cptn\<^sub>e"
| ParCptnEnv: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p(P,s) \<rightarrow>\<^sub>e (P,t);(\<Gamma>,(P, t)#xs) \<in> par_cptn\<^sub>e \<rbrakk> \<Longrightarrow>(\<Gamma>,(P,s)#(P,t)#xs) \<in> par_cptn\<^sub>e"
| ParCptnComp: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>p\<^sub>e(P,s) \<rightarrow> (Q,t); (\<Gamma>,(Q,t)#xs) \<in> par_cptn\<^sub>e \<rbrakk> \<Longrightarrow> (\<Gamma>,(P,s)#(Q,t)#xs) \<in> par_cptn\<^sub>e"
  
lemma par_cptn\<^sub>e_cptn:"(\<Gamma>,xs) \<in> par_cptn\<^sub>e \<Longrightarrow> (\<Gamma>,xs) \<in> par_cptn"
proof(induct rule: par_cptn\<^sub>e.induct)
  case (ParCptnOne \<Gamma> P s)
  then show ?case
    by (blast intro: par_cptn.ParCptnOne) 
next
  case (ParCptnEnv \<Gamma> P s t xs)
  then show ?case
    by (blast intro: par_cptn.ParCptnEnv) 
next
  case (ParCptnComp \<Gamma> e P s Q t xs)
  then show ?case
    using  steppe_stepp by (blast intro:par_cptn.ParCptnComp)
qed 
 
lemma par_cptn_cptn\<^sub>e:"(\<Gamma>,xs) \<in> par_cptn \<Longrightarrow> (\<Gamma>,xs) \<in> par_cptn\<^sub>e"
proof(induct rule: par_cptn.induct)
  case (ParCptnOne \<Gamma> P s)
  then show ?case
    by (blast intro: par_cptn\<^sub>e.ParCptnOne) 
next
  case (ParCptnEnv \<Gamma> P s t xs)
  then show ?case
    by (blast intro: par_cptn\<^sub>e.ParCptnEnv) 
next
  case (ParCptnComp \<Gamma> P s Q t xs)
  then show ?case
    using  stepp_steppe by (blast intro:par_cptn\<^sub>e.ParCptnComp)
qed 
    

lemma par_cptn_eq:"par_cptn\<^sub>e = par_cptn"  
  using par_cptn_cptn\<^sub>e par_cptn\<^sub>e_cptn by fastforce
  
 inductive_cases par_cptn_e_elim_cases [cases set]:
"(\<Gamma>, [(P,s)]) \<in> par_cptn\<^sub>e"
"(\<Gamma>,(P,s)#(Q,t)#xs) \<in> par_cptn\<^sub>e"

lemma cptne_append_is_cptne [rule_format]: 
 "\<forall>b a. (\<Gamma>,b#c1)\<in>par_cptn\<^sub>e \<longrightarrow>  (\<Gamma>,a#c2)\<in>par_cptn\<^sub>e \<longrightarrow> (b#c1)!length c1=a \<longrightarrow> (\<Gamma>,b#c1@c2)\<in>par_cptn\<^sub>e"
apply(induct c1)
 apply simp
apply clarify
apply(erule par_cptn\<^sub>e.cases,simp_all)
apply (simp add: par_cptn\<^sub>e.ParCptnEnv)
  by (simp add: par_cptn\<^sub>e.ParCptnComp)  

lemma par_cptn_e_dest:"(\<Gamma>,(P,s)#(Q,t)#xs) \<in> par_cptn\<^sub>e \<Longrightarrow> (\<Gamma>,(Q,t)#xs)\<in> par_cptn\<^sub>e"
by (auto dest: par_cptn_e_elim_cases)

lemma par_cptn_e_dest_pair:"(\<Gamma>,x#x1#xs) \<in> par_cptn\<^sub>e \<Longrightarrow> (\<Gamma>,x1#xs)\<in> par_cptn\<^sub>e"
proof -
  assume "(\<Gamma>,x#x1#xs) \<in> par_cptn\<^sub>e"
  thus ?thesis using par_cptn_e_dest prod.collapse by metis
qed

lemma par_cptn_e_dest1:"(\<Gamma>,(P,s)#(Q,t)#xs) \<in> par_cptn\<^sub>e \<Longrightarrow> (\<Gamma>,(P,s)#[(Q,t)])\<in> par_cptn\<^sub>e"
proof -
  assume a1: "(\<Gamma>, (P, s) # (Q, t) # xs) \<in> par_cptn\<^sub>e"
  have "(\<Gamma>, [(Q, t)]) \<in> par_cptn\<^sub>e"
    by (meson ParCptnOne)
  thus ?thesis
    by (metis a1 par_cptn\<^sub>e.ParCptnComp par_cptn\<^sub>e.ParCptnEnv par_cptn_e_elim_cases(2))       
qed


lemma par_cptn_dest1_pair:"(\<Gamma>,x#x1#xs) \<in> par_cptn\<^sub>e \<Longrightarrow> (\<Gamma>,x#[x1])\<in> par_cptn\<^sub>e"
proof -
  assume "(\<Gamma>,x#x1#xs) \<in> par_cptn\<^sub>e"
  thus ?thesis using par_cptn_e_dest1 prod.collapse by metis
qed


lemma par_cptn_dest_2:
  "(\<Gamma>,a#xs@ys) \<in> par_cptn\<^sub>e  \<Longrightarrow> (\<Gamma>,a#xs)\<in> par_cptn\<^sub>e"
proof (induct "xs" arbitrary: a)
  case Nil thus ?case using par_cptn\<^sub>e.simps by fastforce 
next
  case (Cons x xs') 
  then have "(\<Gamma>,a#[x])\<in>par_cptn\<^sub>e" by (simp add: par_cptn_dest1_pair)
  also have "(\<Gamma>, x # xs') \<in> par_cptn\<^sub>e"
    using Cons.hyps Cons.prems 
    by (metis append_Cons par_cptn_e_dest_pair)    
  ultimately show ?case using cptne_append_is_cptne [of \<Gamma> a "[x]" x xs']
    by force    
qed   
    
lemma droppar_cptne_is_par_cptne [rule_format]:
  "\<forall>j<length c. (\<Gamma>,c) \<in> par_cptn\<^sub>e \<longrightarrow> (\<Gamma>,drop j c) \<in> par_cptn\<^sub>e"
apply(induct "c")
 apply(force elim: par_cptn\<^sub>e.cases)
apply clarify
apply(case_tac j,simp+)
apply(erule par_cptn\<^sub>e.cases)
  apply simp
 apply force
apply force
  done  
    
lemma par_assum_tail:
  assumes a0:"c =  (\<Gamma>,(p,l)#xs)" and 
          a1:"\<forall>i. Suc i<length (snd c) \<longrightarrow> 
              (fst c)\<turnstile>\<^sub>p((snd c)!i)  \<rightarrow>\<^sub>e ((snd c)!(Suc i)) \<longrightarrow>        
              (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> rely" and
          a2:"c1 = (\<Gamma>,xs)"
    shows "\<forall>i. Suc i<length (snd c1) \<longrightarrow> 
              (fst c1)\<turnstile>\<^sub>p((snd c1)!i)  \<rightarrow>\<^sub>e ((snd c1)!(Suc i)) \<longrightarrow>        
              (snd((snd c1)!i), snd((snd c1)!(Suc i))) \<in> rely"
  using a0 a1 a2 by fastforce
          
  
definition par_cp\<^sub>e :: "('s,'p,'f,'e) body \<Rightarrow> ('s,'p,'f,'e) par_Simpl \<Rightarrow> 
                  ('s,'f) xstate \<Rightarrow> (('s,'p,'f,'e) par_confs) set" where
  "par_cp\<^sub>e \<Gamma> P s \<equiv> {(\<Gamma>1,l). l!0=(P,s) \<and> (\<Gamma>,l) \<in> par_cptn\<^sub>e \<and> \<Gamma>1=\<Gamma>}"  

lemma eq_par_cp\<^sub>e_par_cp:"par_cp\<^sub>e \<Gamma> P s = par_cp \<Gamma> P s" 
  using par_cptn_eq unfolding par_cp\<^sub>e_def par_cp_def by auto
  
lemma par_cp_l_dest:"(\<Gamma>, l) \<in> par_cp\<^sub>e \<Gamma> c s \<Longrightarrow>  
       \<exists>l'. l = (c,s)#l'" 
unfolding par_cp\<^sub>e_def 
proof-
  assume "(\<Gamma>, l) \<in> {(\<Gamma>1, ls). ls ! 0 = (c, s) \<and> (\<Gamma>, ls) \<in> par_cptn\<^sub>e \<and> \<Gamma>1 = \<Gamma>}"
  then have l:"l!0 = (c,s) \<and> (\<Gamma>, l) \<in> par_cptn\<^sub>e" by auto
  thus ?thesis proof (cases l)
    case Nil thus ?thesis using l par_cptn\<^sub>e.simps by auto
  next 
    case (Cons la lh) thus ?thesis using l par_cptn\<^sub>e.simps by auto
  qed
qed
      
lemma par_cptn\<^sub>e_take_suc_i:
  "(\<Gamma>, l)\<in> par_cptn\<^sub>e \<Longrightarrow>
   i < length l \<Longrightarrow>
   k = length l - i -1 \<Longrightarrow>
  (\<Gamma>, (take (i+1) l)) \<in> par_cptn\<^sub>e"
proof(induct k arbitrary:l i)
  case 0 thus ?case by auto    
next
  case (Suc k)
  then obtain a l1 where l:"l = a #l1"
    by (metis gr_implies_not_zero list.exhaust_sel list.size(3)) 
  {
   assume "i=0" then have ?case
   proof -
     have "(\<Gamma>, take 1 l) \<in> par_cptn\<^sub>e"
       by (metis (no_types) One_nat_def Suc.prems(1) neq_Nil_conv 
           par_cptn\<^sub>e.ParCptnOne surj_pair take_Suc_Cons take_eq_Nil)
     then show ?thesis
       by (simp add: \<open>i = 0\<close>)
   qed 
  } note l1 = this
  { assume "i>0"    
    then obtain i' where "i = i'+1"
      by (metis Suc_diff_1 Suc_eq_plus1) 
    then have ?case using Suc l
      by (metis Suc_eq_plus1 append_take_drop_id par_cptn_dest_2 take_Suc_Cons)
  } thus ?case using l1 by auto
qed   
  
lemma par_cptn\<^sub>e_take_i:
  "(\<Gamma>, l)\<in> par_cptn\<^sub>e \<Longrightarrow>
   i < length l \<Longrightarrow>   
  (\<Gamma>, (take (i+1) l)) \<in> par_cptn\<^sub>e"
using par_cptn\<^sub>e_take_suc_i by auto
    
lemma par_cp\<^sub>e_app:
  assumes a0:"(\<Gamma>, (c',s')#l') \<in> par_cp\<^sub>e \<Gamma> c' s'" and
          a1:"(\<Gamma>, l) \<in> par_cp\<^sub>e \<Gamma> c s \<and> l!i = (c', s') \<and> i<length l"
  shows "(\<Gamma>, (take (i+1) l) @ l') \<in> par_cp\<^sub>e \<Gamma> c s"
proof-
  have "l!0 = (c,s) \<and> (\<Gamma>, l)\<in> par_cptn\<^sub>e" using a1 unfolding par_cp\<^sub>e_def by auto
  then have "(\<Gamma>, (take (i+1) l) ) \<in> par_cptn\<^sub>e" using a1 par_cptn\<^sub>e_take_suc_i by auto
  then obtain a b where take_ab:"(take (i+1) l) = a#b" using par_cptn\<^sub>e.simps by blast 
  also then have  "(a#b)!length b = (c',s')" using a1    
  proof -
    have f1: "Suc i = i + Suc 0"
      by presburger
    have f2: "\<forall>n ps. \<not> n < length ps \<or> (ps ! n) # drop (Suc n) ps = drop n ps"
      using Cons_nth_drop_Suc by blast
    then have "length (take i l) + (length (drop (i + 1) l) + Suc 0) = 
               length ((a # b) @ drop (i + 1) l)" using f1 
      by (metis (no_types) One_nat_def a1 
                append_take_drop_id take_ab length_append list.size(4))
    then have "length (take i l) = length b" by force
    then show ?thesis
      by (metis One_nat_def a1 f1 nth_append_length take_Suc_conv_app_nth take_ab)       
  qed
  ultimately show ?thesis using a0 cptne_append_is_cptne unfolding par_cp\<^sub>e_def
  proof -
    assume a1: "(\<Gamma>, (c', s') # l') \<in> {(\<Gamma>1, l). l ! 0 = (c', s') \<and> (\<Gamma>, l) \<in> par_cptn\<^sub>e \<and> \<Gamma>1 = \<Gamma>}"
    have "(\<Gamma>, a # b) \<in> par_cptn\<^sub>e"
      using \<open>(\<Gamma>, take (i + 1) l) \<in> par_cptn\<^sub>e\<close> \<open>take (i + 1) l = a # b\<close> by auto
    then have f2: "(\<Gamma>, a # b @ l') \<in> par_cptn\<^sub>e"
      using a1 by (simp add: \<open>(a # b) ! length b = (c', s')\<close> cptne_append_is_cptne)
    have "0 < length (a # b)"
      by blast
    then have "(take (i + 1) l @ l') ! 0 = l ! 0"
      by (metis (no_types) \<open>take (i + 1) l = a # b\<close> append_take_drop_id nth_append)
    then show "(\<Gamma>, take (i + 1) l @ l') \<in> {(f, ps). ps ! 0 = (c, s) \<and> (\<Gamma>, ps) \<in> par_cptn\<^sub>e \<and> f = \<Gamma>}"
      using f2 \<open>l ! 0 = (c, s) \<and> (\<Gamma>, l) \<in> par_cptn\<^sub>e\<close> \<open>take (i + 1) l = a # b\<close> by auto
  qed  
qed
  
lemma par_cp\<^sub>e_app1:
  assumes a0:"(\<Gamma>, l') \<in> par_cp\<^sub>e \<Gamma> c' s'" and
          a1:"(\<Gamma>, l) \<in> par_cp\<^sub>e \<Gamma> c s \<and> l!i = (c', s') \<and> i<length l"
  shows "(\<Gamma>, (take i l) @ l') \<in> par_cp\<^sub>e \<Gamma> c s"
proof-
  obtain l'' where l:"l'= (c',s')#l''"  unfolding par_cp\<^sub>e_def
    using a0 par_cp_l_dest by blast 
  then have "(\<Gamma>, (take (i+1) l) @ l'') \<in> par_cp\<^sub>e \<Gamma> c s"
    using par_cp\<^sub>e_app a1 a0 by blast
  thus ?thesis using a1 l
  proof -
    have f1: "drop i l = (c', s') # drop (Suc i) l"
      by (metis (no_types) Cons_nth_drop_Suc a1)
    have "take (i + 1) l = take i l @ take (Suc 0) (drop i l)"
      by (metis One_nat_def take_add)
    then show ?thesis
      using f1 \<open>(\<Gamma>, take (i + 1) l @ l'') \<in> par_cp\<^sub>e \<Gamma> c s\<close> l by force
  qed 
qed
  
                                         
lemma tau_tran_closure_cptn: 
  assumes a0:"\<Gamma>\<turnstile>\<^sub>p (c,s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c',s')"          
  shows "\<exists>l. (\<Gamma>,l) \<in>par_cp\<^sub>e \<Gamma> c s \<and> last l = (c',s')"
  using a0
proof  (induct rule: rtranclp_induct[case_names Refl Step] )
  case Refl       
   show ?case unfolding par_cp\<^sub>e_def using par_cptn\<^sub>e.intros(1)[of _ c s] by force
 next
   case (Step a1 a2) 
   then obtain c1 s1 c2 s2 where a1:"a1=(c1,s1) \<and> a2=(c2,s2)" by fastforce   
   with Step have c1_cptn:"(\<Gamma>,(c1,s1)#[(c2,s2)])\<in>par_cptn\<^sub>e" using par_cptn\<^sub>e.intros by fastforce
   from Step obtain l1 where cs_cptn:"(\<Gamma>,(c,s)#l1) \<in> par_cptn\<^sub>e" and 
                             last:"last ((c,s)#l1) = (c1,s1)" 
     unfolding par_cp\<^sub>e_def using a1
     by (metis (mono_tags, lifting) Product_Type.Collect_case_prodD Step.hyps(3) par_cp\<^sub>e_def par_cp_l_dest snd_conv) 
   have "(\<Gamma>, (c, s) # l1 @ [(c2, s2)]) \<in> par_cptn\<^sub>e" using a1 cptne_append_is_cptne[OF cs_cptn c1_cptn] last
     unfolding par_cp\<^sub>e_def by (simp add: last_length) 
   thus ?case using a1 unfolding par_cp\<^sub>e_def by force
 qed


lemma append_assume_R: assumes     
  a0:  "(\<Gamma>, l\<^sub>s) \<in> par_cp\<^sub>e \<Gamma> c (Normal \<sigma>) \<and>
        last l\<^sub>s = (c, Normal \<sigma>n) \<and>
        (\<forall>i. Suc i < length l\<^sub>s \<longrightarrow> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (l\<^sub>s ! i) \<rightarrow>\<^sub>e (l\<^sub>s ! Suc i) \<longrightarrow> (snd (l\<^sub>s ! i), snd (l\<^sub>s ! Suc i)) \<in> R)" and
  a1: "l' =  l\<^sub>s@[(c,Normal \<sigma>n')]" and
  a2:"(Normal \<sigma>n, Normal \<sigma>n')\<in> R"            
shows "(\<forall>i. Suc i < length l' \<longrightarrow> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (l' ! i) \<rightarrow>\<^sub>e (l' ! Suc i) \<longrightarrow> (snd (l' ! i), snd (l' ! Suc i)) \<in> R)"
proof -
  {fix i
    assume a00:"Suc i < length l'" and
     a01:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (l' ! i) \<rightarrow>\<^sub>e (l' ! Suc i)" 
    then have "(snd (l' ! i), snd (l' ! Suc i)) \<in> R" 
    proof-
    {assume "i<length l\<^sub>s" 
      then have ?thesis using a0 a1 a00 a01
        by (metis (no_types, lifting) Suc_lessI a2 diff_Suc_1 last_conv_nth length_0_conv nat.simps(3) 
               nth_append nth_append_length snd_conv)
    } 
    moreover {assume "i\<ge>length l\<^sub>s"     
     then have ?thesis using a1 a2 a0 a00 by auto 
    } ultimately show ?thesis by fastforce
    qed
  } thus ?thesis by auto
qed

 
lemma tau_tran_env_closure_cptn: assumes a0: "\<Gamma>\<turnstile>\<^sub>p (c, Normal \<sigma>) \<rightarrow>\<^sub>e\<^sup>* (c, Normal \<sigma>')"
  shows "\<exists>l\<^sub>s. (\<Gamma>,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma> c (Normal \<sigma>) \<and> last l\<^sub>s = (c,Normal \<sigma>') "
  using a0
proof  (induct rule: rtranclp_induct[case_names Refl Step] )
  case Refl       
   show ?case unfolding par_cp\<^sub>e_def using par_cptn\<^sub>e.intros(1)[of _ c "Normal \<sigma>"] by force
 next
   case (Step a1 a2) 
   then obtain c1 s1 c2 s2 where a1:"a1=(c1,s1) \<and> a2=(c2,s2)" by fastforce   
   then obtain s1n s2n where a1:"a1=(c1,Normal s1n) \<and> a2=(c1,Normal s2n)" 
     using step_pe_elim_cases[OF Step(2)[simplified a1]] by fastforce
   have "(\<Gamma>,[(c1,Normal s2n)])\<in>par_cptn\<^sub>e" using par_cptn\<^sub>e.intros  by auto
   then  
   have c1_cptn:"(\<Gamma>,(c1,Normal s1n)#[(c1,Normal s2n)])\<in>par_cptn\<^sub>e" 
     using  Step(1)   Step(3) par_cptn\<^sub>e.intros(2)[OF Step(2)[simplified a1]] by fastforce
    
   from Step obtain l1 where cs_cptn:"(\<Gamma>,(c,Normal \<sigma>)#l1) \<in> par_cptn\<^sub>e" and 
                             last:"last ((c,Normal \<sigma>)#l1) = (c1,Normal s1n)" 
     unfolding par_cp\<^sub>e_def using a1
     by (metis (mono_tags, lifting) Product_Type.Collect_case_prodD Step.hyps(3) par_cp\<^sub>e_def par_cp_l_dest snd_conv) 
   have "(\<Gamma>, (c, Normal \<sigma>) # l1 @ [(c1, Normal s2n)]) \<in> par_cptn\<^sub>e" using a1 cptne_append_is_cptne[OF cs_cptn c1_cptn] last
     unfolding par_cp\<^sub>e_def by (simp add: last_length) 
   thus ?case using a1 unfolding par_cp\<^sub>e_def by force
 qed
 
lemma id_R_rtrancl_trancl:"\<forall>a. (a,a)\<in>R \<Longrightarrow> R\<^sup>*=R\<^sup>+"
  by (metis equalityI prod.exhaust r_into_rtrancl r_into_trancl' subsetI trancl_rtrancl_absorb transitive_closure_trans(8))

lemma R_cptn:
  assumes a0:"\<forall>\<sigma>. (\<sigma>,\<sigma>)\<in>R" and a1:"R \<subseteq> \<alpha>\<^sub>x" and
          a2:"(Normal \<sigma>, \<sigma>') \<in> R\<^sup>*" and a3:"\<sigma>' = Normal \<sigma>n'"
        shows "\<exists>l\<^sub>s. (\<Gamma>,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma> c (Normal \<sigma>) \<and> last l\<^sub>s = (c,Normal \<sigma>n') \<and> 
               (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                 (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R)"
proof-   
  have a2:"(Normal \<sigma>,  \<sigma>') \<in> R\<^sup>+" using a2 a0 id_R_rtrancl_trancl by auto    
  show ?thesis using a2 a3
proof  (induct arbitrary: \<sigma>n' rule: Transitive_Closure.trancl_induct[case_names Refl Step] )
  case (Refl \<sigma>' )
  then have "(\<Gamma>, [(c,Normal \<sigma>n')])\<in> par_cptn\<^sub>e"  using par_cptn\<^sub>e.intros(1)[of _ c "Normal \<sigma>n'"] by force  
  moreover have "\<Gamma>\<turnstile>\<^sub>p (c, Normal \<sigma>) \<rightarrow>\<^sub>e (c, Normal \<sigma>n')" using ParEnv by force    
  ultimately show ?case unfolding par_cp\<^sub>e_def using par_cptn\<^sub>e.intros(2)  Refl by force        
next
  case (Step \<sigma>' \<sigma>'')
  obtain \<sigma>n where \<sigma>n:"\<sigma>' = Normal \<sigma>n" using a1 Step(2,4) Normal_alpha2 by fastforce
  then obtain l\<^sub>s where l:" (\<Gamma>, l\<^sub>s) \<in> par_cp\<^sub>e \<Gamma> c (Normal \<sigma>) \<and>
          last l\<^sub>s = (c, Normal \<sigma>n) \<and>
          (\<forall>i. Suc i < length l\<^sub>s \<longrightarrow> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (l\<^sub>s ! i) \<rightarrow>\<^sub>e (l\<^sub>s ! Suc i) \<longrightarrow> (snd (l\<^sub>s ! i), snd (l\<^sub>s ! Suc i)) \<in> R)"
    using Step(3) by auto     
  then have "(\<Gamma>, (c, Normal \<sigma>n)#[(c,Normal \<sigma>n')])\<in> par_cptn\<^sub>e"  
    using par_cptn\<^sub>e.intros(2) par_cptn\<^sub>e.intros(1) ParEnv by fastforce  
  then have l':"(\<Gamma>, l\<^sub>s@[(c,Normal \<sigma>n')])\<in> par_cptn\<^sub>e" using l
    by (metis (no_types, lifting) append_Cons case_prodD cptne_append_is_cptne last_length mem_Collect_eq par_cp\<^sub>e_def par_cp_l_dest) 
  moreover have "last (l\<^sub>s@[(c,Normal \<sigma>n')]) = (c, Normal \<sigma>n')" by auto
  moreover have "(l\<^sub>s@[(c,Normal \<sigma>n')]) ! 0 = (c, Normal \<sigma>)" using l unfolding par_cp\<^sub>e_def
    using l par_cp_l_dest by fastforce
  ultimately show ?case using append_assume_R[OF l _ Step(2)[simplified \<sigma>n Step(4)], of "l\<^sub>s @ [(c, Normal \<sigma>n')]"] 
    using l unfolding par_cp\<^sub>e_def by auto
  qed
qed
  



   
lemma l_append:
  assumes 
      a0:"i<length l" 
    shows "l!i = (l@l1)!i "
  by (simp add:  a0 nth_append)
  
lemma add_l: assumes 
  a0:"Suc i = length l" and
  a1:"last l = (c1, s1)" 
 shows "(l @ [(c2, s2)]) ! i = (c1, s1) \<and>
       (l @ [(c2, s2)]) ! Suc i = (c2, s2)"
proof -
 
  have "\<forall>ps n. \<exists>psa p. (Suc n \<noteq> length ps \<or> length psa = n) \<and> 
               (Suc n \<noteq> length ps \<or> (p::'a \<times> 'b) # psa = ps)"
    by (metis Suc_length_conv)
  then show ?thesis
    using a0 a1  by (metis (no_types) last_length lessI 
                     nth_append nth_append_length)
qed
lemma assum_union:
  assumes a0:"\<forall>i. Suc i < length l \<longrightarrow> 
                  \<Gamma>\<^sub>s\<turnstile>\<^sub>p l ! i \<rightarrow>\<^sub>e (l ! Suc i) \<longrightarrow> 
                 (snd (l ! i), snd (l ! Suc i)) \<in> R"  and
          a1:"\<forall>i. Suc i < length l' \<longrightarrow> 
                   \<Gamma>\<^sub>s\<turnstile>\<^sub>p l' ! i \<rightarrow>\<^sub>e (l' ! Suc i) \<longrightarrow> 
                  (snd (l' ! i), snd (l' ! Suc i)) \<in> R" and
          a2:"j<length l \<and> l!j = l'!0"
   shows "\<forall>i. Suc i<length ((take j l)@ l') \<longrightarrow> 
               \<Gamma>\<^sub>s\<turnstile>\<^sub>p(((take j l)@ l')!i)  \<rightarrow>\<^sub>e (((take j l)@ l')!(Suc i)) \<longrightarrow>        
               (snd(((take j l)@ l')!i), snd(((take j l)@ l')!(Suc i))) \<in> R"
proof-   
       
  { assume "j=0"
    then have ?thesis using a1 by auto
  } note l = this
  {
    assume j:"j>0"
    then have eq:"\<forall>i<j. ((take j l)@ l')!i = l!i" using a2 by (simp add: nth_append)         
    {fix i
     assume a00: "Suc i<length ((take j l)@ l')" and
            a01: "\<Gamma>\<^sub>s\<turnstile>\<^sub>p(((take j l)@ l')!i)  \<rightarrow>\<^sub>e (((take j l)@ l')!(Suc i))"      
     {assume "Suc i<j"
       then have "(snd ((take j l @ l') ! i), snd ((take j l @ l') ! Suc i)) \<in> R" 
         using a0 a2 a01 by (simp add: nth_append)
     } note l1 = this
     {assume suc:"Suc i = j"       
       then have "(take j l @ l') ! i = l!i" using eq by simp          
       also have " (take j l @ l') ! j = l'!0" 
         using a2 a00 suc str3[of "take j l" _ l'] by auto       
       ultimately have "(snd ((take j l @ l') ! i), snd ((take j l @ l') ! Suc i)) \<in> R" 
         using a2 a0 suc  a01 by auto          
     } note l2 =this
     {
       assume suc:"Suc i > j"  
       have l:"length (take j l) = j" using a2 by auto
       then have "(take j l @ l') ! i = l'!(i-j)" using a00 str3[of "take j l" _ l'] suc  by auto
       moreover have "(take j l @ l') ! Suc i = l'!((Suc i)-j)" using str3[of "take j l" _ l'] a00 suc l by auto
       ultimately have "(snd ((take j l @ l') ! i), snd ((take j l @ l') ! Suc i)) \<in> R" 
         using a1 suc l a00 a01
         by (simp add: a2 Suc_diff_le less_Suc_eq_le)    
     }
     then have "(snd(((take j l)@ l')!i), snd(((take j l)@ l')!(Suc i))) \<in> R" 
       using l1 l2 by fastforce   
   } then have ?thesis by auto 
   then have ?thesis by auto
  } thus ?thesis using l by fastforce
qed
  
lemma assum_union_comp_tran:
  assumes a0:"\<forall>i. Suc i < length l \<longrightarrow> 
                  \<Gamma>\<turnstile>\<^sub>p l ! i \<rightarrow>\<^sub>e (l ! Suc i) \<longrightarrow> 
                 (snd (l ! i), snd (l ! Suc i)) \<in> R"  and
          a1:"\<forall>i. Suc i < length l' \<longrightarrow> 
                   \<Gamma>\<turnstile>\<^sub>p l' ! i \<rightarrow>\<^sub>e (l' ! Suc i) \<longrightarrow> 
                  (snd (l' ! i), snd (l' ! Suc i)) \<in> R" and
          a2:"last l = (c',s') \<and> l'!0 = (c'',s'') \<and> \<Gamma>\<turnstile>\<^sub>p\<^sub>a (c',s') \<rightarrow> (c'',s'')"
   shows "\<forall>i. Suc i<length (l@ l') \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>p((l@ l')!i)  \<rightarrow>\<^sub>e ((l@ l')!(Suc i)) \<longrightarrow>        
               (snd((l@ l')!i), snd((l@ l')!(Suc i))) \<in> R"
proof - 
    {      
      fix i
      assume a01:"Suc i<length (l@l')" and
             a02: "\<Gamma>\<turnstile>\<^sub>p((l@l')!i)  \<rightarrow>\<^sub>e ((l@l')!(Suc i))"
      have not_env:"\<not> \<Gamma>\<turnstile>\<^sub>p (c',s')  \<rightarrow>\<^sub>e (c'',s'')" using a2
        by (metis  env_pe_c_c'_false nth_list_update_eq step_change_p_or_eq_s step_pev_pair_elim_cases stepce_stepc)
      {
        assume a001: "Suc i< length l" 
        then have "l!i = (l@l')!i \<and>
              l!(Suc i) = (l@l')!(Suc i)"
          using l_append[of _ l l'] by fastforce      
        then have "(snd((l@l')!i), snd((l@l')!(Suc i))) \<in> R"
          using  a0 a02 a001 by auto
      } note l1 = this
      {
        assume a001: "Suc i = length l"         
        then have "l = [] \<longrightarrow> (l @ l') ! i = (c', s')"
            by auto
        then have "(l@l')!i = (c',s') \<and>
                   (l@l')!(Suc i) = (c'',s'')"
          using a2 a001
          by (metis cancel_comm_monoid_add_class.diff_cancel diff_Suc_1 
                    last_conv_nth lessI nth_append order_less_irrefl)
        then have "(snd((l@l')!i), snd((l@l')!(Suc i))) \<in> R" 
          using not_env a2 a02 a001 by auto
      } note l2= this
      { assume a001: "Suc i > length l"
        then obtain k where k:"i = length l + k"          
          using less_imp_Suc_add by auto          
        also have "\<forall>i. (l@l') ! (length l + i) =
                        l'!i" by auto
        ultimately have "(l@l')!i = l'!k \<and>
                         (l@l')!Suc i = l'!Suc k"
          by (metis add_Suc_right)        
        then have "(snd((l@l')!i), snd((l@l')!(Suc i))) \<in> R" 
         using a1 a01 a02  k by auto
      }
      then have "(snd((l@l')!i), snd((l@l')!(Suc i))) \<in> R"
        using l1 l2 a02 not_env by fastforce
    } thus ?thesis by auto
qed

lemma tau_tran_closure_cptn1: 
  assumes a0:"\<Gamma>\<turnstile>\<^sub>p (c,s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c',s')"          
  shows "\<exists>l. (\<Gamma>,l) \<in>par_cp\<^sub>e \<Gamma> c s \<and> 
             (\<forall>i. Suc i<length l \<longrightarrow> 
                       \<Gamma>\<turnstile>\<^sub>p(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>        
                       (snd(l!i), snd(l!(Suc i))) \<in> R) \<and> 
             last l = (c',s')"
  using a0
proof  (induct rule: rtranclp_induct[case_names Refl Step] )
  case Refl       
   show ?case unfolding par_cp\<^sub>e_def using par_cptn\<^sub>e.intros(1)[of _ c s] by force
 next
   case (Step a1 a2) 
   then obtain c1 s1 c2 s2 where a1:"a1=(c1,s1) \<and> a2=(c2,s2)" by fastforce   
   with Step have c1_cptn:"(\<Gamma>,(c1,s1)#[(c2,s2)])\<in>par_cptn\<^sub>e" using par_cptn\<^sub>e.intros by fastforce
   from Step obtain l1 where cs_cptn:"(\<Gamma>,(c,s)#l1) \<in> par_cptn\<^sub>e" and 
                             all_r: "(\<forall>i. Suc i<length ((c,s)#l1) \<longrightarrow> 
                                          \<Gamma>\<turnstile>\<^sub>p(((c,s)#l1)!i)  \<rightarrow>\<^sub>e (((c,s)#l1)!(Suc i)) \<longrightarrow>        
                                          (snd(((c,s)#l1)!i), snd(((c,s)#l1)!(Suc i))) \<in> R)" and
                             last:"last ((c,s)#l1) = (c1,s1)" 
     unfolding par_cp\<^sub>e_def using a1
     by (metis (mono_tags, lifting) Product_Type.Collect_case_prodD  par_cp\<^sub>e_def par_cp_l_dest snd_conv) 
   have "(\<Gamma>, (c, s) # l1 @ [(c2, s2)]) \<in> par_cptn\<^sub>e" using a1 cptne_append_is_cptne[OF cs_cptn c1_cptn] last
     unfolding par_cp\<^sub>e_def by (simp add: last_length)
   also have "(\<forall>i. Suc i<length ((c, s) # l1 @ [(c2, s2)]) \<longrightarrow> 
                      \<Gamma>\<turnstile>\<^sub>p(((c, s) # l1 @ [(c2, s2)])!i)  \<rightarrow>\<^sub>e (((c, s) # l1 @ [(c2, s2)])!(Suc i)) \<longrightarrow>        
                      (snd(((c, s) # l1 @ [(c2, s2)])!i), snd(((c, s) # l1 @ [(c2, s2)])!(Suc i))) \<in> R)"
   using assum_union_comp_tran[OF all_r, of "[(c2,s2)]" c1 s1 c2 s2]  last Step(2) a1 by fastforce   
   ultimately show ?case using a1 unfolding par_cp\<^sub>e_def  by force
qed  
  
  
  
lemma evnt_tran_closure_cptn: 
  assumes a0:"\<Gamma>\<turnstile>\<^sub>p\<^sub>e (c,s) \<rightarrow>\<^sup>+ (cf,sf)"
  shows "\<exists>l. (\<Gamma>,l) \<in>par_cp\<^sub>e \<Gamma> c s \<and>
             last l = (cf,sf)"
proof-
  obtain c' s' c'' s'' where a0:"\<Gamma>\<turnstile>\<^sub>p (c,s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c',s') \<and>  
                               (\<exists>a. a = Some e \<and> \<Gamma>\<turnstile>\<^sub>p\<^sub>a (c',s') \<rightarrow> (c'',s'')) \<and> 
                                \<Gamma>\<turnstile>\<^sub>p (c'',s'') \<rightarrow>\<^sub>\<tau>\<^sup>* (cf,sf)" using a0 by auto
  then obtain l1 l2 where "(\<Gamma>,(c,s)#l1) \<in>par_cp\<^sub>e \<Gamma> c s " and lastl1:"last ((c,s)#l1) = (c',s')" and
                          "(\<Gamma>,(c'',s'')#l2) \<in>par_cp\<^sub>e \<Gamma> c'' s''" and lastl2:"last ((c'',s'')#l2) = (cf,sf)" 
    using tau_tran_closure_cptn  by (metis par_cp_l_dest)                     
  then have l1:"(\<Gamma>,(c,s)#l1)\<in>par_cptn\<^sub>e" and
            l2:"(\<Gamma>,(c'',s'')#l2) \<in>par_cptn\<^sub>e" 
    unfolding par_cp\<^sub>e_def by auto   
  have c:"(\<Gamma>,(c',s')#[(c'',s'')])\<in>par_cptn\<^sub>e" using a0
    by (simp add: a0 par_cptn\<^sub>e.ParCptnComp par_cptn\<^sub>e.ParCptnOne)
 then have cl2:"(\<Gamma>,(c',s')#(c'',s'')#l2) \<in>par_cptn\<^sub>e" and 
           "last ((c',s')#(c'',s'')#l2) = (cf,sf)" 
   using cptne_append_is_cptne[OF c l2] lastl2 by auto
  then have "(\<Gamma>,(c,s)#l1@((c'',s'')#l2)) \<in>par_cptn\<^sub>e" and 
            "last ((c,s)#l1@((c'',s'')#l2)) = (cf,sf)" 
   using cptne_append_is_cptne[OF l1 cl2] lastl1 
   by (auto simp add: last_length lastl2)   
  thus  ?thesis  unfolding par_cp\<^sub>e_def by force
qed
  
lemma evnt_tran_closure_cptn1: 
  assumes a0:"\<Gamma>\<turnstile>\<^sub>p\<^sub>e (c,s) \<rightarrow>\<^sup>+ (cf,sf)"
  shows "\<exists>l. (\<Gamma>,l) \<in>par_cp\<^sub>e \<Gamma> c s \<and>
             (\<forall>i. Suc i<length l \<longrightarrow> 
                       \<Gamma>\<turnstile>\<^sub>p(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>        
                       (snd(l!i), snd(l!(Suc i))) \<in> R) \<and>
             last l = (cf,sf)"
proof-
  obtain c' s' c'' s'' where a0:"\<Gamma>\<turnstile>\<^sub>p (c,s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c',s') \<and>  
                               (\<exists>a. a = Some e \<and> \<Gamma>\<turnstile>\<^sub>p\<^sub>a (c',s') \<rightarrow> (c'',s'')) \<and> 
                                \<Gamma>\<turnstile>\<^sub>p (c'',s'') \<rightarrow>\<^sub>\<tau>\<^sup>* (cf,sf)" using a0 by auto
  then obtain l1 l2 where "(\<Gamma>,(c,s)#l1) \<in>par_cp\<^sub>e \<Gamma> c s " and
                    envl1:    "(\<forall>i. Suc i<length ((c,s)#l1) \<longrightarrow> 
                                \<Gamma>\<turnstile>\<^sub>p(((c,s)#l1)!i)  \<rightarrow>\<^sub>e (((c,s)#l1)!(Suc i)) \<longrightarrow>        
                                (snd(((c,s)#l1)!i), snd(((c,s)#l1)!(Suc i))) \<in> R)" and
                     lastl1:"last ((c,s)#l1) = (c',s')" and
                          "(\<Gamma>,(c'',s'')#l2) \<in>par_cp\<^sub>e \<Gamma> c'' s''" and 
                      envl2:    "(\<forall>i. Suc i<length ((c'',s'')#l2) \<longrightarrow> 
                                \<Gamma>\<turnstile>\<^sub>p(((c'',s'')#l2)!i)  \<rightarrow>\<^sub>e (((c'',s'')#l2)!(Suc i)) \<longrightarrow>        
                                (snd(((c'',s'')#l2)!i), snd(((c'',s'')#l2)!(Suc i))) \<in> R)" and
                     lastl2:"last ((c'',s'')#l2) = (cf,sf)" 
    using tau_tran_closure_cptn1  by (metis par_cp_l_dest)                     
  then have l1:"(\<Gamma>,(c,s)#l1)\<in>par_cptn\<^sub>e" and
            l2:"(\<Gamma>,(c'',s'')#l2) \<in>par_cptn\<^sub>e" 
    unfolding par_cp\<^sub>e_def by auto   
  have env:"(\<forall>i. Suc i<length ((c,s)#l1@((c'',s'')#l2)) \<longrightarrow> 
            \<Gamma>\<turnstile>\<^sub>p(((c,s)#l1@((c'',s'')#l2))!i)  \<rightarrow>\<^sub>e (((c,s)#l1@((c'',s'')#l2))!(Suc i)) \<longrightarrow>        
           (snd(((c,s)#l1@((c'',s'')#l2))!i), snd(((c,s)#l1@((c'',s'')#l2))!(Suc i))) \<in> R)"  
  using assum_union_comp_tran[OF envl1 envl2, of c' s' c'' s''] lastl1 a0 by fastforce  
  have c:"(\<Gamma>,(c',s')#[(c'',s'')])\<in>par_cptn\<^sub>e" using a0
    by (simp add: a0 par_cptn\<^sub>e.ParCptnComp par_cptn\<^sub>e.ParCptnOne)
 then have cl2:"(\<Gamma>,(c',s')#(c'',s'')#l2) \<in>par_cptn\<^sub>e" and 
           "last ((c',s')#(c'',s'')#l2) = (cf,sf)" 
   using cptne_append_is_cptne[OF c l2] lastl2 by auto
  then have "(\<Gamma>,(c,s)#l1@((c'',s'')#l2)) \<in>par_cptn\<^sub>e" and 
            "last ((c,s)#l1@((c'',s'')#l2)) = (cf,sf)" 
   using cptne_append_is_cptne[OF l1 cl2] lastl1 
   by (auto simp add: last_length lastl2)   
  thus  ?thesis using env unfolding par_cp\<^sub>e_def by force
qed

definition sim_final_state :: "('a, 'p, 'f, 'e) LanguageCon.com list \<Rightarrow>
                               ('a, 'f) xstate \<Rightarrow>
                               ('b, 'p, 'f, 'e) LanguageCon.com list \<Rightarrow>                                
                               ('b, 'f) xstate \<Rightarrow>                                 
                               ('a,'b) invs \<Rightarrow> 
                               ('a,'b) invs \<Rightarrow> bool"
where
"sim_final_state c\<^sub>c s\<^sub>c c\<^sub>s s\<^sub>s \<gamma>n \<gamma>a \<equiv> 
  (\<not> (\<exists>i<length c\<^sub>c.  c\<^sub>c!i = Throw) \<and> \<not> (\<exists>i<length c\<^sub>s.  c\<^sub>s!i = Throw) \<and> ((\<exists>scn ssn. s\<^sub>c = Normal scn \<and> s\<^sub>s = Normal ssn \<and> (scn,ssn)\<in>\<gamma>n) \<or>
                                     (\<exists>f. s\<^sub>c = Fault f \<and> s\<^sub>s = Fault f) \<or> 
                                     (s\<^sub>c = Stuck \<and> s\<^sub>s = Stuck ) \<or> 
                                     (\<exists>sca ssa. s\<^sub>c = Abrupt sca \<and> s\<^sub>s = Abrupt ssa))) \<or>
  ((\<exists>i<length c\<^sub>c. c\<^sub>c!i = Throw) \<and> (\<exists>i<length c\<^sub>s.  c\<^sub>s!i = Throw) \<and> (\<exists>scn ssn. s\<^sub>c = Normal scn \<and> s\<^sub>s = Normal ssn \<and> (scn,ssn)\<in>\<gamma>a))"  
    

lemma last_skip_ref1:
  assumes 
   a0: "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and
   a1:"\<sigma> = Normal \<sigma>n \<and> (\<forall>i<length c\<^sub>c. c\<^sub>c!i = Skip) \<and> 0 < length c\<^sub>c"
  shows 
   "\<exists>l\<^sub>s.   (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and>
           (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                     \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                     (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
           (\<forall>i<length (fst (last l\<^sub>s)). fst (last l\<^sub>s)!i = Skip) \<and> 
           (\<exists>\<Sigma>n'. snd(last l\<^sub>s) = Normal \<Sigma>n' \<and> 
                   (\<sigma>n,\<Sigma>n') \<in>\<gamma>\<^sub>q \<and> 0 < length (fst (last l\<^sub>s)))"
proof-
 obtain \<Sigma>n' c\<^sub>s' where "((((\<sigma>, \<sigma>),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
        (\<sigma>n, \<Sigma>n')\<in>\<gamma>\<^sub>q \<and> \<gamma>\<^sub>q\<subseteq>\<alpha> \<and> \<sigma> = Normal \<sigma>n \<and>
        \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and> (\<forall>i<length c\<^sub>s'. c\<^sub>s'!i = Skip) \<and> 0 < length c\<^sub>s')"
   using a1 par_sim_elim_cases[OF a0]
   by force
 thus ?thesis using tau_tran_closure_cptn1
   by (metis fst_conv snd_conv)     
qed  
  
  
lemma last_skip_ref:  
  assumes 
   a0: "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and
   a1:"\<sigma> = Normal \<sigma>n \<and> (\<forall>i<length c\<^sub>c. c\<^sub>c!i = Skip) \<and> 0 < length c\<^sub>c"
  shows 
   "\<exists>l\<^sub>s.   (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and>
           (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                     \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                     (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and>
           final_c (fst (last l\<^sub>s),snd(last l\<^sub>s)) \<and> 0 < length (fst (last l\<^sub>s)) \<and> 
               sim_final_state c\<^sub>c \<sigma> (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a"
  using last_skip_ref1[OF a0 a1] a1  
   unfolding sim_final_state_def final_c_def final_def by auto

lemma last_Throw_ref1:
  assumes 
   a0: "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and
   a1:"(final_c (c\<^sub>c,\<sigma>)  \<and> \<sigma> = Normal \<sigma>n \<and> (\<exists>i<length c\<^sub>c. c\<^sub>c!i = Throw))"
  shows 
   "\<exists>l\<^sub>s. (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and>
           (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                     \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                     (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
           final_c (fst (last l\<^sub>s),snd(last l\<^sub>s)) \<and>  0 < length (fst (last l\<^sub>s)) \<and> 
          (\<exists>\<Sigma>n' i. snd(last l\<^sub>s) = Normal \<Sigma>n' \<and>
              i<length (fst (last l\<^sub>s)) \<and>  (fst (last l\<^sub>s))!i = Throw \<and> (\<sigma>n ,\<Sigma>n') \<in>\<gamma>\<^sub>a)"
proof-
 have "\<exists>\<Sigma>n' c\<^sub>s'. ((\<sigma>, \<sigma>), \<Sigma>, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>a \<and>
                \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
                \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and> final_c (c\<^sub>s', Normal \<Sigma>n') \<and> 
                (\<exists>i<length c\<^sub>s'. c\<^sub>s' ! i = LanguageCon.com.Throw)"
   using a1 par_sim_elim_cases[OF a0]
   by auto
 then obtain \<Sigma>n' c\<^sub>s' where "((\<sigma>, \<sigma>), \<Sigma>, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>a \<and>
                \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
                \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and> final_c (c\<^sub>s', Normal \<Sigma>n') \<and> 
                (\<exists>i<length c\<^sub>s'. c\<^sub>s' ! i = LanguageCon.com.Throw)"
   by auto
 then obtain l\<^sub>s where "(\<Gamma>\<^sub>s, l\<^sub>s) \<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and>
          (\<forall>i. Suc i < length l\<^sub>s \<longrightarrow> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (l\<^sub>s ! i) \<rightarrow>\<^sub>e (l\<^sub>s ! Suc i) \<longrightarrow> (snd (l\<^sub>s ! i), snd (l\<^sub>s ! Suc i)) \<in> R\<^sub>s) \<and>
          final_c (fst (last l\<^sub>s), snd(last l\<^sub>s)) \<and> (\<exists>i. snd(last l\<^sub>s) = Normal \<Sigma>n' \<and>
          i<length (fst (last l\<^sub>s)) \<and> fst (last l\<^sub>s) ! i = LanguageCon.com.Throw) \<and> (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>a "
   using tau_tran_closure_cptn1  by (metis (mono_tags, lifting) fst_conv snd_conv) 
  also then have "0 < length (fst (last l\<^sub>s))" by fastforce
 ultimately show ?thesis by auto           
qed  
  
lemma last_Throw_ref:
assumes 
 a0: "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and
 a1:"(final_c (c\<^sub>c,\<sigma>)  \<and> \<sigma> = Normal \<sigma>n \<and> (\<exists>i<length c\<^sub>c. c\<^sub>c!i = Throw))"
shows 
 "\<exists>l\<^sub>s.   (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and>
         (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                   \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                   (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
         final_c (fst (last l\<^sub>s),snd(last l\<^sub>s)) \<and>  0 < length (fst (last l\<^sub>s)) \<and>
            sim_final_state c\<^sub>c \<sigma> (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a"
 using last_Throw_ref1[OF a0 a1] a1 unfolding sim_final_state_def by auto 
      
lemma last_not_normal_ref1:
  assumes 
   a0: "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and
   a1:"\<forall>\<sigma>n. \<sigma> \<noteq> Normal \<sigma>n  \<and> (\<forall>i<length c\<^sub>c. c\<^sub>c!i = Skip) \<and> 0 < length c\<^sub>c"
  shows 
   "\<exists>l\<^sub>s.   (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and>
           (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                     \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                     (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
           (\<forall>i<length (fst (last l\<^sub>s)). fst (last l\<^sub>s)!i = Skip) \<and> (\<sigma>,snd(last l\<^sub>s))\<in>\<alpha>\<^sub>x 
            \<and> 0 < length (fst (last l\<^sub>s))"
proof-  
   have "(\<exists>\<Sigma>' c\<^sub>s'.
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<and>
                 (\<sigma>, \<Sigma>') \<in> \<alpha>\<^sub>x \<and> (\<forall>i<length c\<^sub>s'. c\<^sub>s' ! i = LanguageCon.com.Skip) \<and> c\<^sub>s' \<noteq> [])"
    using a1 par_sim_elim_cases[OF a0] 
    by auto
  then obtain \<Sigma>' c\<^sub>s' where "  \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<and>
                 (\<sigma>, \<Sigma>') \<in> \<alpha>\<^sub>x \<and> (\<forall>i<length c\<^sub>s'. c\<^sub>s' ! i = LanguageCon.com.Skip) \<and> c\<^sub>s' \<noteq> []"
    by auto 
 thus ?thesis using tau_tran_closure_cptn1 using a1
   by (metis (mono_tags, lifting) fst_conv length_greater_0_conv snd_conv)  
qed  

lemma last_not_normal_ref:
assumes 
 a0: "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and
 a1:"\<forall>\<sigma>n. \<sigma> \<noteq> Normal \<sigma>n  \<and> (\<forall>i<length c\<^sub>c. c\<^sub>c!i = Skip) \<and> 0 < length c\<^sub>c"
shows 
 "\<exists>l\<^sub>s.   (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and>
         (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                   \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                   (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and>
         final_c (fst (last l\<^sub>s),snd(last l\<^sub>s)) \<and> 0 < length (fst (last l\<^sub>s)) \<and>
         sim_final_state c\<^sub>c \<sigma> (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a"
  using last_not_normal_ref1[OF a0 a1] a1   
  unfolding sim_final_state_def final_c_def final_def alpha_xstate_def
  by (cases \<sigma>, auto)
  
lemma All_End_simulation:
  assumes 
   a0: "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and 
   a1:"All_End (c\<^sub>c,\<sigma>)"
  shows 
   "\<exists>l\<^sub>s.   (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and>
           (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                     \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                     (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
           All_End (last l\<^sub>s) \<and>  sim_final_state c\<^sub>c \<sigma> (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a"
proof-  
  have c_not_empty: "c\<^sub>c \<noteq>[] \<and> (\<forall>i<length c\<^sub>c. final (c\<^sub>c!i,\<sigma>))" using a1 unfolding All_End_def by auto
  { 
    assume "\<forall>i<length c\<^sub>c. c\<^sub>c!i = Skip" 
    then have ?thesis 
      using c_not_empty last_skip_ref[OF a0]   last_not_normal_ref[OF a0]            
      unfolding All_End_def final_def final_c_def
      apply (cases \<sigma>) apply  auto by fastforce
  } note l =this
  {
    assume "\<not> (\<forall>i<length c\<^sub>c. c\<^sub>c!i = Skip)" 
    then have "final_c (c\<^sub>c,\<sigma>)  \<and> (\<exists>ns. \<sigma> = Normal ns) \<and> (\<exists>i<length c\<^sub>c. c\<^sub>c!i = Throw)"
      using c_not_empty
      unfolding final_c_def final_def by auto
    then have ?thesis 
      using last_Throw_ref[OF a0]  
      unfolding final_c_def All_End_def by fastforce
  }
  thus ?thesis using l by auto
qed  
  

  
  
  definition par_comm\<^sub>e :: 
  "(('s,'f) tran) set \<times> 
   ('s set \<times> 's set) \<Rightarrow>
   'f set \<Rightarrow> 
     (('s,'p,'f,'e) par_confs) set" where
  "par_comm\<^sub>e \<equiv> \<lambda>(guar, (q,a)) F. 
     {c. snd (last (snd c)) \<notin> Fault ` F \<longrightarrow> 
         (\<forall>i e. 
            Suc i<length (snd c) \<longrightarrow> 
            ((fst c)\<turnstile>\<^sub>p\<^sub>e((snd c)!i)  \<rightarrow> ((snd c)!(Suc i))) \<longrightarrow>                        
              (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> guar) \<and> 
                (All_End (last (snd c)) \<longrightarrow> 
                   (\<exists>j<length (fst (last (snd c))). fst (last (snd c))!j=Throw \<and> 
                        snd (last (snd c)) \<in> Normal ` a) \<or>
                   (\<forall>j<length (fst (last (snd c))). fst (last (snd c))!j=Skip \<and>
                        snd (last (snd c)) \<in> Normal ` q))}"

lemma par_comm\<^sub>e_par_comm: 
 "(\<Gamma>,xs)\<in> par_comm\<^sub>e (G,q,a) F \<Longrightarrow> (\<Gamma>,xs)\<in> par_comm (G,q,a) F" 
  unfolding par_comm\<^sub>e_def par_comm_def  
  apply auto
  by (metis prod.collapse stepp_steppe)+

lemma par_comm_par_comm\<^sub>e: 
 "(\<Gamma>,xs)\<in> par_comm (G,q,a) F \<Longrightarrow> (\<Gamma>,xs)\<in> par_comm\<^sub>e (G,q,a) F" 
  unfolding par_comm\<^sub>e_def par_comm_def  
  apply auto
  by (metis prod.collapse steppe_stepp)+
    
lemma par_comm_eq_par_comm\<^sub>e:
  "par_comm (G,q,a) F = par_comm\<^sub>e (G,q,a) F"
  using par_comm\<^sub>e_par_comm par_comm_par_comm\<^sub>e by auto
  
lemma par_comm_tail: 
  assumes a0:"(\<Gamma>, (p1, t) # (p2,s) # xs) \<in> par_comm\<^sub>e (G\<^sub>s, q\<^sub>s, a\<^sub>s) F" 
  shows "(\<Gamma>, (p2,s) # xs) \<in> par_comm\<^sub>e (G\<^sub>s, q\<^sub>s, a\<^sub>s) F"
  using a0 unfolding par_comm\<^sub>e_def  All_End_def final_def by auto
            

        

definition par_com_validity :: 
  "('s,'p,'f,'e) body \<Rightarrow>  'f set \<Rightarrow> ('s,'p,'f,'e) com list\<Rightarrow> 
    's set \<Rightarrow> (('s,'f) tran) set \<Rightarrow>  (('s,'f) tran) set \<Rightarrow>  
    's set \<Rightarrow>  's set \<Rightarrow>  bool" 
    ("_ \<Turnstile>\<^sub>e\<^bsub>'/_\<^esub>/ _ SAT [_,_, _, _,_]" [61,60,0,0,0,0,0,0] 45) where
  "\<Gamma> \<Turnstile>\<^sub>e\<^bsub>/F\<^esub> Pr SAT [p, R, G, q,a] \<equiv> 
   \<forall>s. par_cp\<^sub>e \<Gamma> Pr s \<inter> par_assum(p, R) \<subseteq> par_comm\<^sub>e(G, (q,a)) F"
              

lemma SIM_alpha:
assumes   
  a0:"(\<Gamma>,(c\<^sub>c,Normal \<sigma>n),R,G) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>',(c\<^sub>s,Normal \<Sigma>n),R',G')"
shows "(\<sigma>n,\<Sigma>n) \<in> \<alpha>" 
proof -
  show ?thesis using a0 par_sim_elim_cases(1) by blast
qed

lemma SIM_alpha_x:
assumes   
  a0:"(\<Gamma>,(c\<^sub>c,\<sigma>),R,G) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>',(c\<^sub>s, \<Sigma>),R',G')"
shows "(\<sigma>,\<Sigma>) \<in> \<alpha>\<^sub>x" 
proof -
  show ?thesis using a0 par_sim_elim_cases(1) by blast
qed
 
  
lemma par_comp_step_SIM:
  assumes a0:"\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n')" and
  a1: "\<forall>c\<^sub>c' \<sigma>n'. (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>\<tau> (c\<^sub>c,\<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')) \<longrightarrow> 
             (\<exists>c\<^sub>s' \<Sigma>n'.  \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
              (\<sigma>n', \<Sigma>n')\<in>\<alpha> \<and> 
              (((\<sigma>,Normal \<sigma>n'),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))" and
  a2:"\<forall>v c\<^sub>c' \<sigma>n'. (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>(Some v) (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')) \<longrightarrow> 
             (\<exists> c\<^sub>s' \<Sigma>n'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s', Normal \<Sigma>n') \<and> 
              (\<sigma>n', \<Sigma>n')\<in>\<alpha> \<and> (((\<sigma>,Normal \<sigma>n'),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>  
                (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))"
shows "\<exists>c\<^sub>s' \<Sigma>n'. (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s) \<and> 
                 (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',Normal \<Sigma>n') \<or> (\<exists>v. e=Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s',Normal \<Sigma>n')))"
proof -  
  have "(\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>\<tau> (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n')) \<or>  (\<exists>v. e = Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n'))"
    using a0 by auto
  thus ?thesis
  proof    
    assume "\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>\<tau> (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')"
    thus ?thesis using  a1 by fastforce  
   next
     assume "(\<exists>v. e = Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c',Normal \<sigma>n'))"     
     thus ?thesis using a2 
       by fastforce
  qed    
qed
 

lemma par_step_guarantee:  
  assumes a0:"\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n')" and
 a1: "\<forall>c\<^sub>c' \<sigma>n'. (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>\<tau> (c\<^sub>c,\<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')) \<longrightarrow> 
             (\<exists>c\<^sub>s' \<Sigma>n'.  \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
              (\<sigma>n', \<Sigma>n')\<in>\<alpha> \<and> 
              (((\<sigma>,Normal \<sigma>n'),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))" and
  a2:"\<forall>v c\<^sub>c' \<sigma>n'. (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>(Some v) (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')) \<longrightarrow> 
             (\<exists> c\<^sub>s' \<Sigma>n'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s', Normal \<Sigma>n') \<and> 
              (\<sigma>n', \<Sigma>n')\<in>\<alpha> \<and> (((\<sigma>,Normal \<sigma>n'),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>  
                (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))"
shows "\<exists>c\<^sub>s' \<Sigma>n'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',Normal \<Sigma>n') \<or> (\<exists>v. e=Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s',Normal \<Sigma>n'))) \<and> 
                (\<sigma>n',\<Sigma>n')\<in>\<alpha> \<and> ((\<sigma>,Normal \<sigma>n')\<in>G\<^sub>c)"
proof- 
  have "(\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>\<tau> (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n')) \<or>  (\<exists>v. e = Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n'))"
    using a0 by auto
  thus ?thesis 
  proof
    assume "\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>\<tau> (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')"      
    then show ?thesis using a1 unfolding related_transitions_def by fastforce
  next
    assume "\<exists>v. e = Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c',Normal \<sigma>n')"    
    then obtain v where a0: "e = Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c',Normal \<sigma>n')" by auto
    then have "\<exists>c\<^sub>s' \<Sigma>n'.
               (\<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s', Normal \<Sigma>n')) \<and>
               (\<sigma>n',\<Sigma>n')\<in>\<alpha> \<and> 
                (((\<sigma>,Normal \<sigma>n'),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>)" using a2 by fastforce
    thus ?thesis using a0 unfolding related_transitions_def by blast  
  qed    
qed  

lemma SIM_next_state_normal:
"(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow> 
 \<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n') \<Longrightarrow>
 \<exists>c\<^sub>s' \<Sigma>n'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',Normal \<Sigma>n') \<or> (\<exists>v. e=Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s',Normal \<Sigma>n'))) \<and> 
                (\<sigma>n',\<Sigma>n')\<in>\<alpha> \<and> ((\<sigma>,Normal \<sigma>n')\<in>G\<^sub>c)"
  apply (erule par_sim_elim_cases, frule par_step_guarantee)
  by auto


lemma SIM_next_state_not_normal:  
 "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow> 
 \<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c', \<sigma>') \<Longrightarrow> \<forall>\<sigma>n'. \<sigma>' \<noteq> Normal \<sigma>n' \<Longrightarrow>
 \<exists>\<Sigma>' c\<^sub>s'. (\<sigma>',\<Sigma>')\<in>\<alpha>\<^sub>x \<and> (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>')  \<or> (\<exists>v. e = Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s',\<Sigma>') )) \<and> 
          (\<sigma>, \<sigma>')\<in>G\<^sub>c \<and>
          (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)"   
  apply (erule par_sim_elim_cases)  
  by auto

lemma SIM_guarantee_normal1:  
 "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow> 
 \<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n') \<Longrightarrow>
 \<exists>c\<^sub>s' \<Sigma>n'. (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s) \<and>
     (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',Normal \<Sigma>n') \<or> (\<exists>v. e=Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s',Normal \<Sigma>n')))   
     "    
  by (erule par_sim_elim_cases, drule par_comp_step_SIM, auto)
    
lemma SIM_guarantee_normal:
assumes  
 a0:"(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and 
 a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',Normal \<sigma>n')"
shows "\<exists>c\<^sub>s' \<Sigma>n' l. (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s) \<and>
                  (\<forall>i. Suc i<length l \<longrightarrow> 
                       \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>        
                       (snd(l!i), snd(l!(Suc i))) \<in> R\<^sub>s) \<and>
                  (\<Gamma>\<^sub>s,l) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and> last l = (c\<^sub>s', Normal \<Sigma>n')"
proof-         
  obtain c\<^sub>s' \<Sigma>n' where c1:"(\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)" and 
                 "(\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<or> (\<exists>v. e=Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s',Normal \<Sigma>n')))"   
    using  SIM_guarantee_normal1[OF a0 a1] by blast 
  thus ?thesis using evnt_tran_closure_cptn1[of \<Gamma>\<^sub>s c\<^sub>s \<Sigma> _ c\<^sub>s' "Normal \<Sigma>n'"] 
    tau_tran_closure_cptn1[of \<Gamma>\<^sub>s c\<^sub>s \<Sigma> c\<^sub>s' "Normal \<Sigma>n'"] by blast
qed 



  

lemma SIM_guarantee_not_normal:
assumes  
 a0:"(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and 
 a1:"\<forall>\<sigma>n'. \<sigma>' \<noteq> Normal \<sigma>n'" and
 a2:"\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c', \<sigma>')"
shows "\<exists>c\<^sub>s' \<Sigma>' l. (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s) \<and>
                  (\<forall>i. Suc i<length l \<longrightarrow> 
                       \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>        
                       (snd(l!i), snd(l!(Suc i))) \<in> R\<^sub>s) \<and>
                  (\<Gamma>\<^sub>s,l) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and> last l = (c\<^sub>s', \<Sigma>')"
proof-         
  obtain c\<^sub>s' \<Sigma>' where 
      "(\<sigma>',\<Sigma>')\<in>\<alpha>\<^sub>x \<and> (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>')  \<or> (\<exists>v. e = Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s',\<Sigma>') )) \<and>
       (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)"   
    using  SIM_next_state_not_normal[OF a0 a2 a1] by blast  
  moreover have " \<exists>l. (\<forall>i. Suc i<length l \<longrightarrow> 
                       \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>        
                       (snd(l!i), snd(l!(Suc i))) \<in> R\<^sub>s) \<and>
                  (\<Gamma>\<^sub>s,l) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and> last l = (c\<^sub>s', \<Sigma>')"
  using evnt_tran_closure_cptn1[of \<Gamma>\<^sub>s c\<^sub>s \<Sigma> _ c\<^sub>s' \<Sigma>'] 
    tau_tran_closure_cptn1[of \<Gamma>\<^sub>s c\<^sub>s \<Sigma> c\<^sub>s' \<Sigma>'] calculation  by blast
  ultimately show ?thesis using a1 by blast
qed 

lemma SIM_guarantee:
assumes  
 a0:"(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and 
 a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c', \<sigma>')"
shows "\<exists>c\<^sub>s' \<Sigma>' l. (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s) \<and>
                  (\<forall>i. Suc i<length l \<longrightarrow> 
                       \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>        
                       (snd(l!i), snd(l!(Suc i))) \<in> R\<^sub>s) \<and>
                  (\<Gamma>\<^sub>s,l) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and> last l = (c\<^sub>s', \<Sigma>')"
  
proof (cases \<sigma>')
  case (Normal \<sigma>n)
  then show ?thesis using a1 SIM_guarantee_normal[OF a0] by fastforce
next
  case (Abrupt \<sigma>n)
  then show ?thesis using SIM_guarantee_not_normal[OF a0 _ a1] by fastforce
next case (Fault f)
  then show ?thesis using SIM_guarantee_not_normal[OF a0 _ a1] by fastforce
next case Stuck
  then show ?thesis using SIM_guarantee_not_normal[OF a0 _ a1] by fastforce
qed


lemma SIM_next_state:
  assumes 
a0:"(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and
a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c', \<sigma>')" 
shows  "\<exists>c\<^sub>s' \<Sigma>'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or> (\<exists>v. e=Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s',\<Sigma>'))) \<and> (\<sigma>',\<Sigma>')\<in>\<alpha>\<^sub>x \<and>               
                (\<forall>\<sigma>n'. \<sigma>' = Normal \<sigma>n' \<longrightarrow> (\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n' \<and> (\<sigma>n',\<Sigma>n')\<in>\<alpha> \<and> ((\<sigma>,Normal \<sigma>n')\<in>G\<^sub>c)))"
 proof (cases \<sigma>')
   case (Normal \<sigma>n)     
   then show  ?thesis
     using SIM_next_state_normal[OF a0]   a1
     unfolding alpha_xstate_def by blast              
next
  case (Abrupt \<sigma>n)
  then show ?thesis using SIM_next_state_not_normal[OF a0] a1  unfolding alpha_xstate_def by blast
next case (Fault f)
  then show ?thesis using SIM_next_state_not_normal[OF a0] a1  unfolding alpha_xstate_def by blast
next case Stuck
  then show ?thesis using SIM_next_state_not_normal[OF a0] a1  unfolding alpha_xstate_def by blast
qed

lemma SIM_next_state1:
  assumes 
a0:"(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and
a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c', \<sigma>')" 
shows  "\<exists>c\<^sub>s' \<Sigma>'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or> (\<exists>v. e=Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s',\<Sigma>'))) \<and> (\<sigma>',\<Sigma>')\<in>\<alpha>\<^sub>x \<and>               
                (\<forall>\<sigma>n'. \<sigma>' = Normal \<sigma>n' \<longrightarrow> (\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n' \<and> (\<sigma>n',\<Sigma>n')\<in>\<alpha> )) \<and>
               ((\<sigma>, \<sigma>')\<in> G\<^sub>c)"
 proof (cases \<sigma>')
   case (Normal \<sigma>n)     
   then show  ?thesis
     using SIM_next_state_normal[OF a0]   a1
     unfolding alpha_xstate_def by blast              
next
  case (Abrupt \<sigma>n)
  then show ?thesis using SIM_next_state_not_normal[OF a0] a1  
    unfolding alpha_xstate_def related_transitions_def by blast
next case (Fault f)
  then show ?thesis using SIM_next_state_not_normal[OF a0] a1  
    unfolding alpha_xstate_def related_transitions_def by blast
next case Stuck
  then show ?thesis using SIM_next_state_not_normal[OF a0] a1  
    unfolding alpha_xstate_def related_transitions_def by blast
qed

definition in_rel :: "('b, 'f) rel \<Rightarrow> ('a, 'b) invs \<Rightarrow> ('a,'f) rel"
  where "in_rel r \<alpha> = {(\<sigma>, \<sigma>'). (\<forall>\<sigma>n \<sigma>n'. \<sigma> = Normal \<sigma>n \<and> \<sigma>' = Normal \<sigma>n' \<longrightarrow> (\<forall>\<Sigma>n. (\<sigma>n, \<Sigma>n)\<in>\<alpha> \<longrightarrow> (\<exists>\<Sigma>n'.  (\<sigma>n',\<Sigma>n')\<in>\<alpha> \<and> (Normal \<Sigma>n, Normal \<Sigma>n')\<in>r))) \<and> 
                                   (\<forall>\<sigma>n \<sigma>n'. \<not>(\<sigma> = Normal \<sigma>n \<and> \<sigma>' = Normal \<sigma>n') \<longrightarrow> True)}"


lemma SIM_env:  
  assumes 
  a0:"(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and
  a1:"(\<sigma>,\<sigma>') \<in> R\<^sub>c" and a1':"R\<^sub>c \<subseteq>  in_rel (R\<^sub>s\<^sup>*) \<alpha>" and
  a2:"\<Gamma>\<turnstile>\<^sub>p (c\<^sub>c, \<sigma>) \<rightarrow>\<^sub>e (c'\<^sub>c, \<sigma>')"
shows "\<exists>\<Sigma>' l\<^sub>s. (\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>'),R\<^sub>s,G\<^sub>s) \<and> (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and> last l\<^sub>s = (c\<^sub>s,\<Sigma>') "
proof- 
  have "(\<Gamma>\<^sub>s,[(c\<^sub>s,\<Sigma>)]) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma>" unfolding par_cp\<^sub>e_def  using par_cptn\<^sub>e.intros  by auto
  then have eq_pr:"c\<^sub>c = c'\<^sub>c"
    using a2 env_pe_c_c' by blast
  moreover obtain \<sigma>n \<sigma>n' where \<sigma>n:"\<sigma>=Normal \<sigma>n \<and> \<sigma>' = Normal \<sigma>n' " using a2
    by (meson step_pe_elim_cases)
  then obtain \<Sigma>n where \<Sigma>n:"\<Sigma>=Normal \<Sigma>n \<and> (\<sigma>n,\<Sigma>n)\<in>\<alpha>" using a0
    using dest_SIM_alpha by blast 
  moreover obtain \<Sigma>n' where "(\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and> (Normal \<Sigma>n, Normal \<Sigma>n') \<in> R\<^sub>s\<^sup>*"
  using \<sigma>n a1' a1 \<Sigma>n unfolding in_rel_def by fastforce     
  then have "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)" 
    using \<sigma>n \<Sigma>n a1 a0 dest_SIM_env_step[OF a0] unfolding related_transitions_def alpha_xstate_def by auto
  moreover have "\<exists>l\<^sub>s. (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and> last l\<^sub>s = (c\<^sub>s,Normal \<Sigma>n')"    
  proof-
    have x: "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, Normal \<Sigma>n) \<rightarrow>\<^sub>e\<^sup>* (c\<^sub>s, Normal \<Sigma>n')"
      using ParEnv
      by (simp add: step_pe.intros r_into_rtranclp)
    then show ?thesis using tau_tran_env_closure_cptn[OF x] \<Sigma>n by auto
  qed
  ultimately show ?thesis using a1 a0 unfolding related_transitions_def Id_def par_cp\<^sub>e_def by fastforce
qed

lemma SIM_env1:  
  assumes 
  a0:"(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and
  a1:"(\<sigma>,\<sigma>') \<in> R\<^sub>c" and a1':"R\<^sub>c \<subseteq>  in_rel (R\<^sub>s\<^sup>*) \<alpha>" and
  a2:"\<Gamma>\<turnstile>\<^sub>p (c\<^sub>c, \<sigma>) \<rightarrow>\<^sub>e (c'\<^sub>c, \<sigma>')" and a3:"\<forall>\<Sigma>. (\<Sigma>,\<Sigma>)\<in>R\<^sub>s" and a4:"R\<^sub>s\<subseteq>\<alpha>\<^sub>x"
shows "\<exists>\<Sigma>' l\<^sub>s. (\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>'),R\<^sub>s,G\<^sub>s) \<and>
               (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                 (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
               (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and> last l\<^sub>s = (c\<^sub>s,\<Sigma>') "
proof- 
 
  have "(\<Gamma>\<^sub>s,[(c\<^sub>s,\<Sigma>)]) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma>" unfolding par_cp\<^sub>e_def  using par_cptn\<^sub>e.intros  by auto
  then have eq_pr:"c\<^sub>c = c'\<^sub>c"
    using a2 env_pe_c_c' by blast
  moreover obtain \<sigma>n \<sigma>n' where \<sigma>n:"\<sigma>=Normal \<sigma>n \<and> \<sigma>' = Normal \<sigma>n' " using a2
    by (meson step_pe_elim_cases)
  then obtain \<Sigma>n where \<Sigma>n:"\<Sigma>=Normal \<Sigma>n \<and> (\<sigma>n,\<Sigma>n)\<in>\<alpha>" using a0
    using dest_SIM_alpha by blast 
  moreover obtain \<Sigma>n' where "(\<sigma>n', \<Sigma>n') \<in> \<alpha>" and \<Sigma>:"(Normal \<Sigma>n, Normal \<Sigma>n') \<in> R\<^sub>s\<^sup>*"
  using \<sigma>n a1' a1 \<Sigma>n unfolding in_rel_def by fastforce     
  then have "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)" 
    using \<sigma>n \<Sigma>n a1 a0 dest_SIM_env_step[OF a0] unfolding related_transitions_def alpha_xstate_def by auto
  moreover have "\<exists>l\<^sub>s. (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and> last l\<^sub>s = (c\<^sub>s,Normal \<Sigma>n')"    
  proof-
    have x: "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, Normal \<Sigma>n) \<rightarrow>\<^sub>e\<^sup>* (c\<^sub>s, Normal \<Sigma>n')"
      using ParEnv
      by (simp add: step_pe.intros r_into_rtranclp)
    then show ?thesis using tau_tran_env_closure_cptn[OF x] \<Sigma>n by auto
  qed
  ultimately  show ?thesis using a1 a0 R_cptn[OF a3 a4 \<Sigma>]
    unfolding related_transitions_def Id_def par_cp\<^sub>e_def by fastforce
qed    
  

  
lemma cptn_e:
  assumes a0:"(\<Gamma>, l') \<in> par_cp\<^sub>e \<Gamma> c' s'" and
          a1:"(\<Gamma>, l) \<in> par_cp\<^sub>e \<Gamma> c s \<and> last l = (c', s')"
        shows "(\<Gamma>, (take ((length l) -1) l) @ l') \<in> par_cp\<^sub>e \<Gamma> c s"
  using a0 a1 par_cp\<^sub>e_app1
  by (metis (no_types, lifting) diff_less last_conv_nth 
    length_Cons length_greater_0_conv less_Suc_eq_0_disj less_numeral_extra(1) par_cp_l_dest) 
  
lemma RG_SIM_cp_all_sim:
  assumes            
   a0:"(\<Gamma>\<^sub>c,l\<^sub>c)\<in> par_cp\<^sub>e \<Gamma> c\<^sub>c s\<^sub>c \<and> 
       (\<forall>i. Suc i<length l\<^sub>c \<longrightarrow> 
            \<Gamma>\<^sub>c\<turnstile>\<^sub>p(l\<^sub>c!i)  \<rightarrow>\<^sub>e (l\<^sub>c!(Suc i)) \<longrightarrow>        
            (snd(l\<^sub>c!i), snd(l\<^sub>c!(Suc i))) \<in> R\<^sub>c)" and  a1':"R\<^sub>c \<subseteq>  in_rel (R\<^sub>s\<^sup>*) \<alpha>" and
   a1:"(\<Gamma>\<^sub>c,(c\<^sub>c,s\<^sub>c),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,s\<^sub>s),R\<^sub>s,G\<^sub>s)" 
 shows "\<forall>i. i<length l\<^sub>c \<longrightarrow> (\<exists>c'\<^sub>s s'\<^sub>s. (\<Gamma>\<^sub>c,l\<^sub>c !i ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c'\<^sub>s,s'\<^sub>s),R\<^sub>s,G\<^sub>s))"   
proof -  
   {fix i
    assume a00:"i < length l\<^sub>c" 
    have "(\<Gamma>\<^sub>c,l\<^sub>c)\<in> par_cp\<^sub>e \<Gamma> c\<^sub>c s\<^sub>c \<and>(\<forall>i. Suc i<length l\<^sub>c \<longrightarrow> 
         \<Gamma>\<^sub>c\<turnstile>\<^sub>p(l\<^sub>c!i)  \<rightarrow>\<^sub>e (l\<^sub>c!(Suc i)) \<longrightarrow>        
         (snd(l\<^sub>c!i), snd(l\<^sub>c!(Suc i))) \<in> R\<^sub>c)" using a0 unfolding par_assum_def by auto
    then have "(\<exists>c'\<^sub>s s'\<^sub>s. (\<Gamma>\<^sub>c,l\<^sub>c !i ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c'\<^sub>s,s'\<^sub>s),R\<^sub>s,G\<^sub>s))" using a00 a1 
    proof (induct i arbitrary: l\<^sub>c c\<^sub>c s\<^sub>c c\<^sub>s s\<^sub>s)
      case 0 thus ?case unfolding par_cp\<^sub>e_def
        by auto
    next
      case (Suc i)
      then have l_gt1:"length l\<^sub>c\<ge>1" by auto
      {assume "length l\<^sub>c = 1"
       then have ?case using l_gt1 Suc Suc par_cp\<^sub>e_def by force
      } note l1= this
      { 
      assume l_g1:"length l\<^sub>c>1"
      then have lcptn:"l\<^sub>c!0 = (c\<^sub>c,s\<^sub>c) \<and> (\<Gamma>\<^sub>c,l\<^sub>c) \<in> par_cptn\<^sub>e" 
        using Suc unfolding par_cp\<^sub>e_def by auto
      have "\<exists> c'\<^sub>c s'\<^sub>c lh\<^sub>c. l\<^sub>c = (c\<^sub>c,s\<^sub>c)#(c'\<^sub>c,s'\<^sub>c)#lh\<^sub>c"
      proof -
        obtain a1 a2 lh\<^sub>c where "l\<^sub>c = a1#a2#lh\<^sub>c"using Suc l_g1
          by (metis One_nat_def length_0_conv length_Cons less_not_refl not_less0 remdups_adj.cases)        
        also then have "a1 = (c\<^sub>c,s\<^sub>c)" using Suc(2) unfolding par_cp\<^sub>e_def by auto
        ultimately show ?thesis by auto
      qed 
      then obtain c'\<^sub>c s'\<^sub>c lh\<^sub>c where l:"l\<^sub>c = (c\<^sub>c,s\<^sub>c)#(c'\<^sub>c,s'\<^sub>c)#lh\<^sub>c" by auto
      let ?l'="(c'\<^sub>c,s'\<^sub>c)#lh\<^sub>c"
      have "(\<Gamma>\<^sub>c,?l')\<in> par_cp\<^sub>e \<Gamma> c'\<^sub>c s'\<^sub>c" using Suc(2) l unfolding par_cp\<^sub>e_def
        using par_cptn_e_elim_cases(2)[of \<Gamma>\<^sub>c c\<^sub>c s\<^sub>c c'\<^sub>c s'\<^sub>c lh\<^sub>c] by force 
      moreover have "(\<forall>i. Suc i<length ?l' \<longrightarrow>
                          \<Gamma>\<^sub>c\<turnstile>\<^sub>p(?l'!i)  \<rightarrow>\<^sub>e (?l'!(Suc i)) \<longrightarrow>        
                          (snd(?l'!i), snd(?l'!(Suc i))) \<in> R\<^sub>c)" 
        using Suc(2) l by fastforce      
      moreover have "i < length ((c'\<^sub>c,s'\<^sub>c)#lh\<^sub>c)" using Suc l by auto
      moreover have "\<exists> c'\<^sub>s s'\<^sub>s. (\<Gamma>\<^sub>c,(c'\<^sub>c, s'\<^sub>c),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c'\<^sub>s,s'\<^sub>s),R\<^sub>s,G\<^sub>s)"
      proof -
        obtain e where "(\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,s\<^sub>c)  \<rightarrow> (c'\<^sub>c,s'\<^sub>c)) \<or> \<Gamma>\<turnstile>\<^sub>p (c\<^sub>c,s\<^sub>c) \<rightarrow>\<^sub>e (c'\<^sub>c,s'\<^sub>c)" using l lcptn             
          by (metis par_cptn_e_elim_cases(2) step_pe.intros step_pe_elim_cases)            
        thus ?thesis using SIM_env Suc(4) SIM_guarantee a1'
          by (metis Suc.prems(1) Suc_less_eq l lcptn length_Cons length_greater_0_conv list.simps(3) 
                   nth_Cons_0 nth_Cons_Suc par_cptn_e_elim_cases(2) snd_conv)
      qed        
      ultimately have ?case
        using Suc.hyps l by auto
    } thus ?case using l1 l_gt1 by fastforce
    qed 
  } thus ?thesis by auto
qed    
  
  
lemma RG_SIM_cp_all_sim_l\<^sub>s:    
assumes    
 a0:"(\<Gamma>\<^sub>c,l\<^sub>c)\<in> par_cp\<^sub>e \<Gamma>\<^sub>c c\<^sub>c s\<^sub>c \<and> 
     (\<forall>i. Suc i<length l\<^sub>c \<longrightarrow> 
          \<Gamma>\<^sub>c\<turnstile>\<^sub>p(l\<^sub>c!i)  \<rightarrow>\<^sub>e (l\<^sub>c!(Suc i)) \<longrightarrow>        
          (snd(l\<^sub>c!i), snd(l\<^sub>c!(Suc i))) \<in> R\<^sub>c)" and 
a1:"R\<^sub>s \<subseteq> \<alpha>\<^sub>x" and a2:"R\<^sub>c \<subseteq>  in_rel (R\<^sub>s\<^sup>*) \<alpha>" and a3:"\<forall>\<Sigma>. (\<Sigma>,\<Sigma>)\<in>R\<^sub>s" and
 a4:"(\<Gamma>\<^sub>c,(c\<^sub>c,s\<^sub>c),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,s\<^sub>s),R\<^sub>s,G\<^sub>s)" 
shows "\<exists>l\<^sub>s. (\<Gamma>\<^sub>s,l\<^sub>s)\<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and>
            (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                 (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
             (\<forall>i<length l\<^sub>c. (\<exists>i\<^sub>s<length l\<^sub>s. 
               (\<Gamma>\<^sub>c,l\<^sub>c !i ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,l\<^sub>s!i\<^sub>s,R\<^sub>s,G\<^sub>s) ))"   
 using a0 a4
 proof (induct l\<^sub>c arbitrary: c\<^sub>c s\<^sub>c c\<^sub>s s\<^sub>s)  
   case Nil thus ?case unfolding par_cp\<^sub>e_def using par_cptn\<^sub>e.simps by auto       
 next         
   case (Cons l l\<^sub>c)
   then have lc:"l = (c\<^sub>c,s\<^sub>c)" unfolding par_cp\<^sub>e_def using par_cptn\<^sub>e.simps by auto
   {
     assume l:"l\<^sub>c = Nil" 
      then have "(\<Gamma>\<^sub>c,l ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,s\<^sub>s), R\<^sub>s,G\<^sub>s)" 
        using Cons(2,3)  unfolding par_cp\<^sub>e_def by auto
      also have "(\<Gamma>\<^sub>s,[(c\<^sub>s,s\<^sub>s)])\<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s"  unfolding par_cp\<^sub>e_def
        by (simp add: par_cptn\<^sub>e.ParCptnOne) 
      ultimately have ?case using l by auto      
    }note l1 = this
    { fix c'\<^sub>c s'\<^sub>c lh\<^sub>c
      assume l:"l\<^sub>c = (c'\<^sub>c,s'\<^sub>c)#lh\<^sub>c"
      then have lcptn:"((c\<^sub>c,s\<^sub>c)#(c'\<^sub>c,s'\<^sub>c)#lh\<^sub>c)!0 = (c\<^sub>c,s\<^sub>c) \<and> (\<Gamma>\<^sub>c,(c\<^sub>c,s\<^sub>c)#(c'\<^sub>c,s'\<^sub>c)#lh\<^sub>c)\<in>par_cptn\<^sub>e" 
        using Cons l unfolding par_cp\<^sub>e_def by auto
      then obtain e where tran_c:"(\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,s\<^sub>c)  \<rightarrow> (c'\<^sub>c,s'\<^sub>c)) \<or> 
                                   \<Gamma>\<^sub>c\<turnstile>\<^sub>p (c\<^sub>c,s\<^sub>c) \<rightarrow>\<^sub>e (c'\<^sub>c,s'\<^sub>c)"
        using par_cptn_e_elim_cases(2) by blast                                
      then have "(\<Gamma>\<^sub>c,(c'\<^sub>c,s'\<^sub>c)#lh\<^sub>c)\<in> par_cp\<^sub>e \<Gamma>\<^sub>c c'\<^sub>c s'\<^sub>c" 
        using Cons(2) par_cptn_e_elim_cases(2)[of \<Gamma>\<^sub>c c\<^sub>c s\<^sub>c c'\<^sub>c s'\<^sub>c lh\<^sub>c]              
              case_prodI lcptn
        unfolding par_cp\<^sub>e_def by auto 
      moreover have "(\<forall>i. Suc i<length l\<^sub>c \<longrightarrow> 
                      \<Gamma>\<^sub>c\<turnstile>\<^sub>p(l\<^sub>c!i)  \<rightarrow>\<^sub>e (l\<^sub>c!(Suc i)) \<longrightarrow>        
                      (snd(l\<^sub>c!i), snd(l\<^sub>c!(Suc i))) \<in> R\<^sub>c)"
        using Cons(2) by auto          
       moreover have "\<exists> c'\<^sub>s s'\<^sub>s l\<^sub>s. (\<Gamma>\<^sub>c,(c'\<^sub>c, s'\<^sub>c),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c'\<^sub>s,s'\<^sub>s),R\<^sub>s,G\<^sub>s) 
                     \<and> (\<Gamma>\<^sub>s, l\<^sub>s) \<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and> 
                       (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                            \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                            (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and>
                            last l\<^sub>s = (c'\<^sub>s, s'\<^sub>s)"
         using SIM_env1[OF Cons(3) _ a2 _ a3 a1] SIM_guarantee[OF Cons(3)] Cons(2) tran_c 
         by (metis (no_types, lifting) Suc_less_eq l length_Cons nth_Cons_0 nth_Cons_Suc par_cp_l_dest snd_conv step_pe_elim_cases zero_less_Suc) 
       moreover then  obtain c'\<^sub>s s'\<^sub>s l\<^sub>s where 
         sim:"(\<Gamma>\<^sub>c,(c'\<^sub>c, s'\<^sub>c),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c'\<^sub>s,s'\<^sub>s),R\<^sub>s,G\<^sub>s) \<and> 
              (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                            \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                            (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in>R\<^sub>s) \<and>
              (\<Gamma>\<^sub>s, l\<^sub>s) \<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and> last l\<^sub>s = (c'\<^sub>s, s'\<^sub>s)" by auto  
       ultimately have "\<exists>l\<^sub>s. (\<Gamma>\<^sub>s, l\<^sub>s) \<in> par_cp\<^sub>e \<Gamma>\<^sub>s c'\<^sub>s s'\<^sub>s \<and>
                        (\<forall>i. Suc i < length l\<^sub>s \<longrightarrow>
                             \<Gamma>\<^sub>s\<turnstile>\<^sub>p (l\<^sub>s ! i) \<rightarrow>\<^sub>e (l\<^sub>s ! Suc i) \<longrightarrow>
                            (snd (l\<^sub>s ! i), snd (l\<^sub>s ! Suc i)) \<in> R\<^sub>s) \<and>
                      (\<forall>i<length l\<^sub>c.
                        \<exists>i\<^sub>s<length l\<^sub>s. (\<Gamma>\<^sub>c,l\<^sub>c ! i,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                      (\<Gamma>\<^sub>s,l\<^sub>s ! i\<^sub>s,R\<^sub>s,G\<^sub>s))"    
        using Cons(1) l by metis
      then obtain l1s where induc:"(\<Gamma>\<^sub>s, l1s) \<in> par_cp\<^sub>e \<Gamma>\<^sub>s c'\<^sub>s s'\<^sub>s \<and>
                      (\<forall>i. Suc i < length l1s \<longrightarrow>
                             \<Gamma>\<^sub>s\<turnstile>\<^sub>p (l1s ! i) \<rightarrow>\<^sub>e (l1s ! Suc i) \<longrightarrow>
                            (snd (l1s ! i), snd (l1s ! Suc i)) \<in> R\<^sub>s) \<and>
                      (\<forall>i<length l\<^sub>c.
                        \<exists>i\<^sub>s<length l1s. (\<Gamma>\<^sub>c,l\<^sub>c ! i,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                      (\<Gamma>\<^sub>s,l1s ! i\<^sub>s,R\<^sub>s,G\<^sub>s))" by auto
      then have comp:"(\<Gamma>\<^sub>s,(take ((length l\<^sub>s)-1) l\<^sub>s)@l1s) \<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s" 
        using sim cptn_e by fastforce
      moreover have "\<forall>i. Suc i < length ((take ((length l\<^sub>s)-1) l\<^sub>s)@l1s) \<longrightarrow>
                         \<Gamma>\<^sub>s\<turnstile>\<^sub>p (((take ((length l\<^sub>s)-1) l\<^sub>s)@l1s) ! i) \<rightarrow>\<^sub>e (((take ((length l\<^sub>s)-1) l\<^sub>s)@l1s) ! Suc i) \<longrightarrow>
                         (snd (((take ((length l\<^sub>s)-1) l\<^sub>s)@l1s) ! i), snd (((take ((length l\<^sub>s)-1) l\<^sub>s)@l1s) ! Suc i)) \<in> R\<^sub>s"
      proof-
        have "l1s ! 0 = (c'\<^sub>s,s'\<^sub>s)" using induc par_cp_l_dest by fastforce
        then have "l\<^sub>s ! (length l\<^sub>s - 1) = l1s ! 0" using sim
          by (metis last_conv_nth neq_Nil_conv par_cp_l_dest) 
        then also have "length l\<^sub>s - 1 < length l\<^sub>s"
          using par_cp_l_dest sim by force          
        ultimately show ?thesis  
          using assum_union[ of l\<^sub>s \<Gamma>\<^sub>s R\<^sub>s l1s "length l\<^sub>s - 1"] sim induc by fast
      qed                         
      moreover have "(\<forall>i<length (l # l\<^sub>c).
                  \<exists>i\<^sub>s<length ((take ((length l\<^sub>s)-1) l\<^sub>s)@l1s). (\<Gamma>\<^sub>c,(l # l\<^sub>c) ! i,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                                (\<Gamma>\<^sub>s,((take ((length l\<^sub>s)-1) l\<^sub>s)@l1s) ! i\<^sub>s,R\<^sub>s,G\<^sub>s))"
      proof-
      {fix i            
       assume "i<length (l#l\<^sub>c)"
       {
         assume "i=0"
         then have "(\<Gamma>\<^sub>c,(l # l\<^sub>c) ! i,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
               (\<Gamma>\<^sub>s,(take (length l\<^sub>s - 1) l\<^sub>s @ l1s) !0,R\<^sub>s,G\<^sub>s)" 
           using sim Cons(3) lc                           
           by (metis (no_types) Cons.prems(2) comp lc nth_Cons_0 par_cp_l_dest)                                    
         then have "\<exists>i\<^sub>s<length (take (length l\<^sub>s - 1) l\<^sub>s @ l1s).
                 (\<Gamma>\<^sub>c,(l # l\<^sub>c) ! i,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                 (\<Gamma>\<^sub>s,(take (length l\<^sub>s - 1) l\<^sub>s @ l1s) !
                   i\<^sub>s,R\<^sub>s,G\<^sub>s)" using induc l by force          
       }  note lef =this         
       { assume "i>0"           
         have "i < Suc (length l\<^sub>c)"                       
           using \<open>i < length (l # l\<^sub>c)\<close> by auto             
         then have "\<not> length l\<^sub>c < i"                   
           by (meson not_less_eq)                      
         then have "\<exists>i\<^sub>s<length (take (length l\<^sub>s - 1) l\<^sub>s @ l1s).
              (\<Gamma>\<^sub>c, (l#l\<^sub>c) ! i,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
              (\<Gamma>\<^sub>s,(take (length l\<^sub>s - 1) l\<^sub>s @ l1s) ! i\<^sub>s,R\<^sub>s,G\<^sub>s)"                        
           by (metis (no_types) Suc_diff_1 \<open>0 < i\<close> induc not_less_eq nth_Cons_pos prod.collapse str1)
       }         
       then have "\<exists>i\<^sub>s<length (take (length l\<^sub>s - 1) l\<^sub>s @ l1s).
                 (\<Gamma>\<^sub>c,(l # l\<^sub>c) ! i,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                 (\<Gamma>\<^sub>s,(take (length l\<^sub>s - 1) l\<^sub>s @ l1s) !
                   i\<^sub>s,R\<^sub>s,G\<^sub>s)" using lef by fastforce        
     }thus ?thesis by auto                
   qed                
    ultimately have ?case by fast
  }    
  thus ?case using l1      
    by (metis list.exhaust_sel surjective_pairing)          
qed  
  
  lemma RG_SIM_cp_all_sim_l\<^sub>s_fault:    
assumes    
 a0:"(\<Gamma>\<^sub>c,l\<^sub>c)\<in> par_cp\<^sub>e \<Gamma>\<^sub>c c\<^sub>c s\<^sub>c \<and> 
     (\<forall>i. Suc i<length l\<^sub>c \<longrightarrow> 
          \<Gamma>\<^sub>c\<turnstile>\<^sub>p(l\<^sub>c!i)  \<rightarrow>\<^sub>e (l\<^sub>c!(Suc i)) \<longrightarrow>        
          (snd(l\<^sub>c!i), snd(l\<^sub>c!(Suc i))) \<in> R\<^sub>c)" and     
 a1:"(\<Gamma>\<^sub>c,(c\<^sub>c,s\<^sub>c),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,s\<^sub>s),R\<^sub>s,G\<^sub>s)"  and
 a2:"snd (last l\<^sub>c) \<notin> Fault ` F" and a3:"R\<^sub>s \<subseteq> \<alpha>\<^sub>x" and a4:"R\<^sub>c \<subseteq>  in_rel (R\<^sub>s\<^sup>*) \<alpha>" and a5:"\<forall>\<Sigma>. (\<Sigma>,\<Sigma>)\<in>R\<^sub>s" 
shows "\<exists>l\<^sub>s. (\<Gamma>\<^sub>s,l\<^sub>s)\<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and>
            (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                 (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
             (\<forall>i<length l\<^sub>c. (\<exists>i\<^sub>s<length l\<^sub>s. 
               (\<Gamma>\<^sub>c,l\<^sub>c !i ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,l\<^sub>s!i\<^sub>s,R\<^sub>s,G\<^sub>s) )) \<and>
            snd (last l\<^sub>s) \<notin> Fault ` F"   
 using a0 a1 a2
 proof (induct l\<^sub>c arbitrary: c\<^sub>c s\<^sub>c c\<^sub>s s\<^sub>s)  
   case Nil thus ?case unfolding par_cp\<^sub>e_def using par_cptn\<^sub>e.simps by auto       
 next         
   case (Cons l l\<^sub>c)
   then have lc:"l = (c\<^sub>c,s\<^sub>c)" unfolding par_cp\<^sub>e_def using par_cptn\<^sub>e.simps by auto
   {
     assume l:"l\<^sub>c = Nil" 
      then have sim:"(\<Gamma>\<^sub>c,(c\<^sub>c,s\<^sub>c) ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,s\<^sub>s),R\<^sub>s,G\<^sub>s)" 
        using Cons(2,3)  unfolding par_cp\<^sub>e_def by auto       
      moreover have "(\<Gamma>\<^sub>s,[(c\<^sub>s,s\<^sub>s)])\<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s"  unfolding par_cp\<^sub>e_def
        by (simp add: par_cptn\<^sub>e.ParCptnOne)       
      moreover have "s\<^sub>s \<notin> Fault ` F" 
        using  alpha_not_fault dest_SIM_alpha[OF sim] Cons(4)  l lc by fastforce
      ultimately have ?case using l lc by auto      
    }note l1 = this
    { fix c'\<^sub>c s'\<^sub>c lh\<^sub>c
      assume l:"l\<^sub>c = (c'\<^sub>c,s'\<^sub>c)#lh\<^sub>c"
      then have lcptn:"((c\<^sub>c,s\<^sub>c)#(c'\<^sub>c,s'\<^sub>c)#lh\<^sub>c)!0 = (c\<^sub>c,s\<^sub>c) \<and> (\<Gamma>\<^sub>c,(c\<^sub>c,s\<^sub>c)#(c'\<^sub>c,s'\<^sub>c)#lh\<^sub>c)\<in>par_cptn\<^sub>e" 
        using Cons l unfolding par_cp\<^sub>e_def by auto
      then obtain e where tran_c:"(\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,s\<^sub>c)  \<rightarrow> (c'\<^sub>c,s'\<^sub>c)) \<or> 
                                   \<Gamma>\<^sub>c\<turnstile>\<^sub>p (c\<^sub>c,s\<^sub>c) \<rightarrow>\<^sub>e (c'\<^sub>c,s'\<^sub>c)"
        using par_cptn_e_elim_cases(2) by blast                                
      then have "(\<Gamma>\<^sub>c,(c'\<^sub>c,s'\<^sub>c)#lh\<^sub>c)\<in> par_cp\<^sub>e \<Gamma>\<^sub>c c'\<^sub>c s'\<^sub>c" 
        using Cons(2) par_cptn_e_elim_cases(2)[of \<Gamma>\<^sub>c c\<^sub>c s\<^sub>c c'\<^sub>c s'\<^sub>c lh\<^sub>c]              
              case_prodI lcptn
        unfolding par_cp\<^sub>e_def by auto 
      moreover have "(\<forall>i. Suc i<length l\<^sub>c \<longrightarrow> 
                      \<Gamma>\<^sub>c\<turnstile>\<^sub>p(l\<^sub>c!i)  \<rightarrow>\<^sub>e (l\<^sub>c!(Suc i)) \<longrightarrow>        
                      (snd(l\<^sub>c!i), snd(l\<^sub>c!(Suc i))) \<in> R\<^sub>c)"
        using Cons(2) by auto          
       moreover have "\<exists> c'\<^sub>s s'\<^sub>s l\<^sub>s. (\<Gamma>\<^sub>c,(c'\<^sub>c, s'\<^sub>c),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c'\<^sub>s,s'\<^sub>s),R\<^sub>s,G\<^sub>s) 
                     \<and> (\<Gamma>\<^sub>s, l\<^sub>s) \<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and> 
                       (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                            \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                            (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and>
                            last l\<^sub>s = (c'\<^sub>s, s'\<^sub>s)"         
         using SIM_env1[OF Cons(3) _ a4 _ a5 a3] SIM_guarantee[OF Cons(3)] Cons(2) tran_c
         by (metis (no_types, lifting) Suc_less_eq l length_Cons nth_Cons_0 nth_Cons_Suc par_cp_l_dest snd_conv step_pe_elim_cases zero_less_Suc)  
       moreover then  obtain c'\<^sub>s s'\<^sub>s l\<^sub>s where 
         sim:"(\<Gamma>\<^sub>c,(c'\<^sub>c, s'\<^sub>c),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c'\<^sub>s,s'\<^sub>s),R\<^sub>s,G\<^sub>s) \<and> 
              (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                            \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                            (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and>
              (\<Gamma>\<^sub>s, l\<^sub>s) \<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and> last l\<^sub>s = (c'\<^sub>s, s'\<^sub>s)" 
         by auto  
       moreover have "snd (last l\<^sub>c) \<notin> Fault ` F" using Cons(4) l by auto
       ultimately have "\<exists>l\<^sub>s. (\<Gamma>\<^sub>s, l\<^sub>s) \<in> par_cp\<^sub>e \<Gamma>\<^sub>s c'\<^sub>s s'\<^sub>s \<and>
                        (\<forall>i. Suc i < length l\<^sub>s \<longrightarrow>
                             \<Gamma>\<^sub>s\<turnstile>\<^sub>p (l\<^sub>s ! i) \<rightarrow>\<^sub>e (l\<^sub>s ! Suc i) \<longrightarrow>
                            (snd (l\<^sub>s ! i), snd (l\<^sub>s ! Suc i)) \<in>R\<^sub>s) \<and>
                      (\<forall>i<length l\<^sub>c.
                        \<exists>i\<^sub>s<length l\<^sub>s. (\<Gamma>\<^sub>c,l\<^sub>c ! i,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                      (\<Gamma>\<^sub>s,l\<^sub>s ! i\<^sub>s,R\<^sub>s,G\<^sub>s)) \<and>  
                      snd (last l\<^sub>s) \<notin> Fault ` F"    
        using Cons(1) l by fastforce 
      then obtain l1s where induc:"(\<Gamma>\<^sub>s, l1s) \<in> par_cp\<^sub>e \<Gamma>\<^sub>s c'\<^sub>s s'\<^sub>s \<and>
                      (\<forall>i. Suc i < length l1s \<longrightarrow>
                             \<Gamma>\<^sub>s\<turnstile>\<^sub>p (l1s ! i) \<rightarrow>\<^sub>e (l1s ! Suc i) \<longrightarrow>
                            (snd (l1s ! i), snd (l1s ! Suc i)) \<in> R\<^sub>s) \<and>
                      (\<forall>i<length l\<^sub>c.
                        \<exists>i\<^sub>s<length l1s. (\<Gamma>\<^sub>c,l\<^sub>c ! i,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                      (\<Gamma>\<^sub>s,l1s ! i\<^sub>s,R\<^sub>s,G\<^sub>s)) \<and> snd (last l1s) \<notin> Fault ` F" 
         by auto
      then have comp:"(\<Gamma>\<^sub>s,(take ((length l\<^sub>s)-1) l\<^sub>s)@l1s) \<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s" 
        using sim cptn_e by fastforce
      moreover have "\<forall>i. Suc i < length ((take ((length l\<^sub>s)-1) l\<^sub>s)@l1s) \<longrightarrow>
                         \<Gamma>\<^sub>s\<turnstile>\<^sub>p (((take ((length l\<^sub>s)-1) l\<^sub>s)@l1s) ! i) \<rightarrow>\<^sub>e (((take ((length l\<^sub>s)-1) l\<^sub>s)@l1s) ! Suc i) \<longrightarrow>
                         (snd (((take ((length l\<^sub>s)-1) l\<^sub>s)@l1s) ! i), snd (((take ((length l\<^sub>s)-1) l\<^sub>s)@l1s) ! Suc i)) \<in> R\<^sub>s"
      proof-
        have "l1s ! 0 = (c'\<^sub>s,s'\<^sub>s)" using induc par_cp_l_dest by fastforce
        then have "l\<^sub>s ! (length l\<^sub>s - 1) = l1s ! 0" using sim
          by (metis last_conv_nth neq_Nil_conv par_cp_l_dest) 
        then also have "length l\<^sub>s - 1 < length l\<^sub>s"
          using par_cp_l_dest sim by force          
        ultimately show ?thesis  
          using assum_union[ of l\<^sub>s \<Gamma>\<^sub>s R\<^sub>s l1s "length l\<^sub>s - 1"] sim induc by fast
      qed                         
      moreover have "(\<forall>i<length (l # l\<^sub>c).
                  \<exists>i\<^sub>s<length ((take ((length l\<^sub>s)-1) l\<^sub>s)@l1s). (\<Gamma>\<^sub>c,(l # l\<^sub>c) ! i,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                                (\<Gamma>\<^sub>s,((take ((length l\<^sub>s)-1) l\<^sub>s)@l1s) ! i\<^sub>s,R\<^sub>s,G\<^sub>s))"
      proof-
      {fix i            
       assume "i<length (l#l\<^sub>c)"
       {
         assume "i=0"
         then have "(\<Gamma>\<^sub>c,(l # l\<^sub>c) ! i,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
               (\<Gamma>\<^sub>s,(take (length l\<^sub>s - 1) l\<^sub>s @ l1s) !0,R\<^sub>s,G\<^sub>s)" 
           using sim Cons(3) lc                           
           by (metis (no_types) Cons.prems(2) comp lc nth_Cons_0 par_cp_l_dest)                                    
         then have "\<exists>i\<^sub>s<length (take (length l\<^sub>s - 1) l\<^sub>s @ l1s).
                 (\<Gamma>\<^sub>c,(l # l\<^sub>c) ! i,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                 (\<Gamma>\<^sub>s,(take (length l\<^sub>s - 1) l\<^sub>s @ l1s) !
                   i\<^sub>s,R\<^sub>s,G\<^sub>s)" using induc l by force          
       }  note lef =this         
       { assume "i>0"           
         have "i < Suc (length l\<^sub>c)"                       
           using \<open>i < length (l # l\<^sub>c)\<close> by auto             
         then have "\<not> length l\<^sub>c < i"                   
           by (meson not_less_eq)                      
         then have "\<exists>i\<^sub>s<length (take (length l\<^sub>s - 1) l\<^sub>s @ l1s).
              (\<Gamma>\<^sub>c, (l#l\<^sub>c) ! i,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
              (\<Gamma>\<^sub>s,(take (length l\<^sub>s - 1) l\<^sub>s @ l1s) ! i\<^sub>s,R\<^sub>s,G\<^sub>s)"                        
           by (metis (no_types) Suc_diff_1 \<open>0 < i\<close> induc not_less_eq nth_Cons_pos prod.collapse str1)
       }         
       then have "\<exists>i\<^sub>s<length (take (length l\<^sub>s - 1) l\<^sub>s @ l1s).
                 (\<Gamma>\<^sub>c,(l # l\<^sub>c) ! i,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                 (\<Gamma>\<^sub>s,(take (length l\<^sub>s - 1) l\<^sub>s @ l1s) !
                   i\<^sub>s,R\<^sub>s,G\<^sub>s)" using lef by fastforce        
     }thus ?thesis by auto                
   qed 
   moreover have "snd (last (take (length l\<^sub>s - 1) l\<^sub>s @ l1s)) \<notin> Fault ` F"
     using induc     
     by (metis gr_implies_not0 l last_appendR 
         length_Cons list.size(3) zero_less_Suc)
    ultimately have ?case by fast
  }    
  thus ?case using l1      
    by (metis list.exhaust_sel surjective_pairing)          
qed  



  
lemma RG_SIM_cp_all_sim_l\<^sub>s_All_End:    
assumes    
 a0:"(\<Gamma>\<^sub>c,l\<^sub>c)\<in> par_cp\<^sub>e \<Gamma>\<^sub>c c\<^sub>c s\<^sub>c \<and> 
     (\<forall>i. Suc i<length l\<^sub>c \<longrightarrow> 
          \<Gamma>\<^sub>c\<turnstile>\<^sub>p(l\<^sub>c!i)  \<rightarrow>\<^sub>e (l\<^sub>c!(Suc i)) \<longrightarrow>        
          (snd(l\<^sub>c!i), snd(l\<^sub>c!(Suc i))) \<in> R\<^sub>c)" and     
 a1:"(\<Gamma>\<^sub>c,(c\<^sub>c,s\<^sub>c),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,s\<^sub>s),R\<^sub>s,G\<^sub>s)"  and
 a2:"All_End (last l\<^sub>c)" and a3:"R\<^sub>s \<subseteq> \<alpha>\<^sub>x" and a4:"R\<^sub>c \<subseteq>  in_rel (R\<^sub>s\<^sup>*) \<alpha>" and a5:"\<forall>\<Sigma>. (\<Sigma>,\<Sigma>)\<in>R\<^sub>s"
shows "\<exists>l\<^sub>s. (\<Gamma>\<^sub>s,l\<^sub>s)\<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and>
            (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                 (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
             All_End (last l\<^sub>s) \<and> sim_final_state (fst (last l\<^sub>c)) (snd (last l\<^sub>c)) (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a"  
proof -
  obtain l\<^sub>s where l1:"(\<Gamma>\<^sub>s,l\<^sub>s)\<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and>
            (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                 (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and>              
             (\<forall>i<length l\<^sub>c. (\<exists>i\<^sub>s<length l\<^sub>s. 
               (\<Gamma>\<^sub>c,l\<^sub>c !i ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,l\<^sub>s!i\<^sub>s,R\<^sub>s,G\<^sub>s) ))"  
    using RG_SIM_cp_all_sim_l\<^sub>s[OF a0 a3 a4 a5 a1] by auto
  then obtain i\<^sub>s where iss: "i\<^sub>s<length l\<^sub>s \<and> (\<Gamma>\<^sub>c,(last l\<^sub>c) ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,l\<^sub>s!i\<^sub>s,R\<^sub>s,G\<^sub>s)"
    by (metis a0 last_length length_Cons lessI par_cp_l_dest)
    
  then obtain l\<^sub>s1 where ls1:"(\<Gamma>\<^sub>s,l\<^sub>s1) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s (fst (l\<^sub>s!i\<^sub>s)) (snd (l\<^sub>s!i\<^sub>s)) \<and>
           (\<forall>i. Suc i<length l\<^sub>s1 \<longrightarrow> 
                     \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s1!i)  \<rightarrow>\<^sub>e (l\<^sub>s1!(Suc i)) \<longrightarrow>        
                     (snd(l\<^sub>s1!i), snd(l\<^sub>s1!(Suc i))) \<in> R\<^sub>s) \<and> 
           All_End (last l\<^sub>s1) \<and> sim_final_state (fst (last l\<^sub>c)) (snd (last l\<^sub>c)) (fst (last l\<^sub>s1)) (snd (last l\<^sub>s1)) \<gamma>\<^sub>q \<gamma>\<^sub>a" 
    using All_End_simulation a2
    by (metis surjective_pairing)
  then have "(\<Gamma>\<^sub>s,(take i\<^sub>s l\<^sub>s)@ l\<^sub>s1) \<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s" using l1 par_cp\<^sub>e_app1
    by (metis iss prod.collapse) 
  moreover have "All_End (last ((take i\<^sub>s l\<^sub>s)@ l\<^sub>s1)) \<and> 
                 sim_final_state (fst (last l\<^sub>c)) (snd (last l\<^sub>c)) (fst (last ((take i\<^sub>s l\<^sub>s)@ l\<^sub>s1))) (snd (last ((take i\<^sub>s l\<^sub>s)@ l\<^sub>s1))) \<gamma>\<^sub>q \<gamma>\<^sub>a"
    using ls1 par_cp_l_dest by force
  moreover have "(\<forall>i. Suc i<length ((take i\<^sub>s l\<^sub>s)@ l\<^sub>s1) \<longrightarrow> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>p(((take i\<^sub>s l\<^sub>s)@ l\<^sub>s1)!i)  \<rightarrow>\<^sub>e (((take i\<^sub>s l\<^sub>s)@ l\<^sub>s1)!(Suc i)) \<longrightarrow>        
                 (snd(((take i\<^sub>s l\<^sub>s)@ l\<^sub>s1)!i), snd(((take i\<^sub>s l\<^sub>s)@ l\<^sub>s1)!(Suc i))) \<in> R\<^sub>s)"
    using ls1 l1 assum_union
    by (metis (no_types, lifting) iss nth_Cons_0 par_cp_l_dest prod.collapse)  
  ultimately show ?thesis by auto
qed
  

  
lemma comp_normal_s'_normal_s:
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', Normal s') " 
   shows "\<exists>s1. s= Normal s1"
  using step_m
 apply cases apply auto
  using step_not_normal_not_normal apply blast
  using step_not_normal_not_normal by blast
    
lemma stepe_not_normal_not_normal:
  assumes step:"\<Gamma>\<turnstile>\<^sub>c\<^sub>e (c, s) \<rightarrow> (c', s')"
  shows "\<forall>s1. s\<noteq>Normal s1 \<Longrightarrow> \<forall>s1. s' \<noteq> Normal s1"
using step step_Abrupt step_Stuck step_Fault
  by (induct) auto
    
 lemma compe_normal_s'_normal_s:
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>c\<^sub>v (c, s) \<rightarrow> (c', Normal s') " 
   shows "\<exists>s1. s= Normal s1"
  using step_m
 apply cases apply auto
  using stepe_not_normal_not_normal apply blast
    using stepe_not_normal_not_normal by blast


  
lemma "(\<Gamma>, l) \<in> par_cptn\<^sub>e \<Longrightarrow>
       snd (last l) \<in> (Normal ` UNIV) \<Longrightarrow>       
       i<length l \<Longrightarrow>
       snd (l!i) \<in> (Normal ` UNIV)"
  unfolding par_cp\<^sub>e_def
proof(induction "(length l) - (i+1)" arbitrary: l i)
  case 0 thus ?case
    by (metis Suc_eq_plus1 Suc_lessI diff_Suc_1 gr_implies_not_zero 
              last_conv_nth length_0_conv zero_less_diff)
next
  case (Suc n) 
  then have lenl:"i+1 < length l" by linarith  
  then have i1:"snd (l ! (i+1)) \<in> range Normal" using Suc(1)[OF _ Suc(3) Suc(4)] using Suc(2) by auto
  then have dropi:"(\<Gamma>, drop i l) \<in>par_cptn\<^sub>e"  by (simp add: Suc.prems(1) Suc.prems(3) droppar_cptne_is_par_cptne)       
  then have "drop i l!0 =  l!i \<and> drop i l!(Suc 0) = l!(Suc i)" using lenl by auto
  then obtain lxs where "drop i l = l!i#l!(Suc i)#lxs" using lenl
    by (metis Cons_nth_drop_Suc Suc.prems(3) Suc_eq_plus1)
  then have d:"(\<Gamma>,(fst(l!i),snd(l!i))#(fst(l!(Suc i)),snd(l!(Suc i)))#lxs)\<in>par_cptn\<^sub>e"using dropi by auto
  then have "\<Gamma>\<turnstile>\<^sub>p (l!i) \<rightarrow>\<^sub>e (l!(i+1)) \<or> (\<exists>e. \<Gamma>\<turnstile>\<^sub>p\<^sub>e (l!i) \<rightarrow> (l!(i+1)))" 
    using lenl Suc(3) par_cptn_e_elim_cases(2)[OF d]
    by (metis Suc_eq_plus1 prod.collapse) 
  moreover{
    assume "\<Gamma>\<turnstile>\<^sub>p (l!i) \<rightarrow>\<^sub>e (l!(i+1))"
    then have ?case using i1
      by (metis prod.collapse range_eqI step_pe_elim_cases)
  }
  moreover
  {
    assume "(\<exists>e. \<Gamma>\<turnstile>\<^sub>p\<^sub>e (l!i) \<rightarrow> (l!(i+1)))"
    then obtain e where "\<Gamma>\<turnstile>\<^sub>p\<^sub>e (l!i) \<rightarrow> (l!(i+1))" by auto
    moreover obtain ns where "snd (l!(i+1)) = Normal ns" using i1 calculation by auto
    ultimately have ?case using compe_normal_s'_normal_s
      by (metis prod.collapse range_eqI step_pev_pair_elim_cases) 
  }  
  ultimately show ?case by auto  
qed
        
(* lemma par_comm_all_normal: 
  assumes
      a0:"l!0=(p,s)" and a0':"(\<Gamma>\<^sub>s,l)\<in> par_cptn\<^sub>e " and
      a1:"(\<Gamma>\<^sub>s,l)\<in>par_assum(UNIV,R\<^sub>s)"  and
      a2:"(\<Gamma>\<^sub>s,l) \<in> par_comm\<^sub>e(G\<^sub>s, (q\<^sub>s,a\<^sub>s)) F" and
      a4:"snd (last l) \<notin> Fault ` F"
shows "\<forall>i<length l. snd (l!i) \<in> Normal ` UNIV"     
      
proof-
  {fix i
    assume i:"i<length l"
    have "snd (l!i) \<in> Normal ` UNIV"
      using a0' a0 a1 a2  a4 i
    proof(induct  "i" arbitrary:l p s)
      case 0 thus ?case unfolding par_assum_def by auto
    next
      case (Suc ia)
      then have s_normal:"s\<in> Normal ` UNIV" unfolding par_assum_def by auto
      obtain q t ls where l: "l = (p,s)#(q,t)#ls" using Suc
        by (metis One_nat_def Zero_not_Suc gr_implies_not0 hd_conv_nth 
                  length_Cons less_one list.exhaust_sel list.size(3) surjective_pairing)
      then have lscptn:"(\<Gamma>\<^sub>s,(q,t)#ls)\<in> par_cptn\<^sub>e" using Suc(2)
        using par_cptn_e_dest by blast
      then have env_step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p(p,s) \<rightarrow>\<^sub>e (q,t) \<or> (\<exists>e. \<Gamma>\<^sub>s \<turnstile>\<^sub>p\<^sub>e(p,s) \<rightarrow> (q,t))"
        using par_cptn_e_elim_cases(2) Suc(2) l by blast
      then have t_normal: "t \<in> Normal ` UNIV"
      proof
        assume "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (p, s) \<rightarrow>\<^sub>e (q, t)"
        then show ?thesis using  Suc(4) l
          by (metis (full_types) rangeI step_pe_elim_cases)
      next
        assume "\<exists>e. \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>e (p, s) \<rightarrow> (q, t)"
        then obtain e where "\<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>e (p, s) \<rightarrow> (q, t)" by auto
        then have "(s,t)\<in>G\<^sub>s" using  Suc(5,7) l unfolding par_comm\<^sub>e_def
         by fastforce        
        then show ?thesis using  Suc(5,6,7) l s_normal  using Normal_alpha by fastforce
      qed        
      then have "snd (((q,t)#ls) ! ia) \<in> range Normal"
      proof-                           
        have "(\<Gamma>\<^sub>s, (q,t)#ls) \<in> par_assum (UNIV,R\<^sub>s )"
          using Suc(4) l t_normal unfolding par_assum_def by fastforce
        thus ?thesis using Suc(1,5,6,7,8) l par_comm_tail lscptn
          by (metis (no_types, lifting) Suc_less_eq last.simps length_Cons list.simps(3) nth_Cons_0)   
      qed               
      thus ?case using l by auto
    qed
  } thus ?thesis by auto    
qed *)
  
      

lemma RG_SIM_fst_env_comm_ref1: 
  assumes      
 a0:"(\<forall>i<length l\<^sub>c. \<exists>i\<^sub>s<length l\<^sub>s.(\<Gamma>\<^sub>c,l\<^sub>c !i ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,l\<^sub>s!i\<^sub>s,R\<^sub>s,G\<^sub>s) )" and   
 a2:" Suc i<length l\<^sub>c" and
 a3:"\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e(l\<^sub>c!i)  \<rightarrow> (l\<^sub>c!(Suc i))" and
 a4:"(\<Gamma>\<^sub>s,l\<^sub>s) \<in> par_comm\<^sub>e(G\<^sub>s, (q\<^sub>s,a\<^sub>s)) F" and 
 a7:"snd (last l\<^sub>s) \<notin> Fault ` F" and
 a8:"l\<^sub>s!0=(p,s)" and a9:"(\<Gamma>\<^sub>s,l\<^sub>s)\<in> par_cptn\<^sub>e " and
  a10:"(\<Gamma>\<^sub>s,l\<^sub>s)\<in>par_assum(UNIV,R\<^sub>s)"  
  
shows "(snd(l\<^sub>c!i), snd(l\<^sub>c!(Suc i))) \<in> G\<^sub>c"
proof-
  obtain c\<^sub>c \<sigma> c\<^sub>c' \<sigma>' where l: "l\<^sub>c!i = (c\<^sub>c,\<sigma>) \<and> l\<^sub>c!(Suc i) = (c\<^sub>c',\<sigma>')" by fastforce
  then have step:"\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',\<sigma>')" using a3 by auto
  then obtain i\<^sub>s i\<^sub>s\<^sub>' where sims:"i\<^sub>s<length l\<^sub>s \<and> (\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>) ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,l\<^sub>s!i\<^sub>s,R\<^sub>s,G\<^sub>s)" and
                      islen:"i\<^sub>s\<^sub>'<length l\<^sub>s" and sim1:"(\<Gamma>\<^sub>c,(c\<^sub>c',\<sigma>') ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,l\<^sub>s!i\<^sub>s\<^sub>',R\<^sub>s,G\<^sub>s) " 
    using a0 a2 l by (metis Suc_lessD)  
  then  obtain c\<^sub>s \<Sigma> where ls:"l\<^sub>s!i\<^sub>s=(c\<^sub>s,\<Sigma>)" by fastforce
  then have sim:"(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>) ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)"
    using sims by auto
  obtain c\<^sub>s' \<Sigma>' where guar:"
     (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or> (\<exists>v. e = Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s', \<Sigma>'))) \<and>
     (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<and>
     (\<forall>\<sigma>n'. \<sigma>' = Normal \<sigma>n' \<longrightarrow> (\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n' \<and> (\<sigma>n', \<Sigma>n') \<in> \<alpha>)) \<and> 
     (\<sigma>, \<sigma>') \<in> G\<^sub>c"    
    using SIM_next_state1[OF sim step] by force
  thus ?thesis using l by auto      
qed
       

lemma final_c_lambda1:
  assumes a0:"(\<Gamma>\<^sub>s,l\<^sub>s) \<in> par_comm\<^sub>e(G\<^sub>s, (q\<^sub>s,a\<^sub>s)) F " and
          a1:"snd (last l\<^sub>c) \<notin> Fault ` F" and                    
          a2:"All_End (last l\<^sub>s)" and
          a3: "sim_final_state (fst (last l\<^sub>c)) (snd (last l\<^sub>c)) (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a"
  shows " (\<not>(\<exists>i<length (fst (last l\<^sub>s)).  (fst (last l\<^sub>s))!i = Throw) \<and> snd (last l\<^sub>s) \<in> Normal ` q\<^sub>s) \<or> 
          ((\<exists>i<length (fst (last l\<^sub>s)).  (fst (last l\<^sub>s))!i = Throw) \<and> snd (last l\<^sub>s) \<in> Normal ` a\<^sub>s )"
proof-
  have "snd (last l\<^sub>s) \<notin> Fault ` F" using a1 a3 unfolding sim_final_state_def by auto  
  thus ?thesis using a0 a2 unfolding  par_comm\<^sub>e_def All_End_def by force
qed
  
lemma final_c_lambda2:
  assumes a0:"(\<Gamma>\<^sub>s,l\<^sub>s) \<in> par_comm\<^sub>e(G\<^sub>s, (q\<^sub>s,a\<^sub>s)) F " and
          a1:"snd (last l\<^sub>c) \<notin> Fault ` F" and
          a2: "All_End (last l\<^sub>s)" and          
          a4: "sim_final_state (fst (last l\<^sub>c)) (snd (last l\<^sub>c)) (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a"
  shows "\<exists>qc qs. snd (last l\<^sub>c) = Normal qc \<and> snd (last l\<^sub>s) = Normal qs \<and>
            ((\<not>(\<exists>i<length (fst (last l\<^sub>c)).  (fst (last l\<^sub>c))!i = Throw) \<and> (qc,qs)\<in> \<gamma>\<^sub>q) \<or> 
              ((\<exists>i<length (fst (last l\<^sub>c)).  (fst (last l\<^sub>c))!i = Throw) \<and> (qc,qs)\<in> \<gamma>\<^sub>a))"
using a4 final_c_lambda1[OF a0 a1 a2 a4] unfolding sim_final_state_def by auto      

  lemma final_c_lambda3:
  assumes a0:"(\<Gamma>\<^sub>s,l\<^sub>s) \<in> par_comm\<^sub>e(G\<^sub>s, (q\<^sub>s,a\<^sub>s)) F " and
          a1:"snd (last l\<^sub>c) \<notin> Fault ` F" and
          a2: "All_End (last l\<^sub>s)" and
          a3: "\<gamma>qn = \<Down>\<^sub>i\<gamma>\<^sub>q \<and> q\<^sub>s \<subseteq> Domain \<gamma>qn \<and> ((\<gamma>qn `` q\<^sub>s) \<subseteq> q\<^sub>c) \<and>
               \<gamma>an = \<Down>\<^sub>i\<gamma>\<^sub>a \<and> a\<^sub>s \<subseteq> Domain \<gamma>an \<and> ((\<gamma>an `` a\<^sub>s) \<subseteq> a\<^sub>c)" and
          a4: "sim_final_state (fst (last l\<^sub>c)) (snd (last l\<^sub>c)) (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a"
  shows " (\<not>(\<exists>i<length (fst (last l\<^sub>c)).  (fst (last l\<^sub>c))!i = Throw) \<and> snd (last l\<^sub>c) \<in> Normal ` q\<^sub>c) \<or> 
          ((\<exists>i<length (fst (last l\<^sub>c)).  (fst (last l\<^sub>c))!i = Throw) \<and> snd (last l\<^sub>c) \<in> Normal ` a\<^sub>c )"
proof -
  have comm_ls:" (\<not>(\<exists>i<length (fst (last l\<^sub>s)).  (fst (last l\<^sub>s))!i = Throw) \<and> snd (last l\<^sub>s) \<in> Normal ` q\<^sub>s) \<or> 
          ((\<exists>i<length (fst (last l\<^sub>s)).  (fst (last l\<^sub>s))!i = Throw) \<and> snd (last l\<^sub>s) \<in> Normal ` a\<^sub>s )"
    using final_c_lambda1[OF a0 a1 a2 a4] by auto
 { assume a00:"\<not>(\<exists>i<length (fst (last l\<^sub>c)).  (fst (last l\<^sub>c))!i = Throw)"    
    obtain ns\<^sub>c  where  nsc:"snd (last l\<^sub>c) = Normal ns\<^sub>c" 
      using a4 a00 comm_ls unfolding sim_final_state_def by auto      
    moreover obtain ns\<^sub>s where nssq:"snd (last l\<^sub>s) = Normal ns\<^sub>s \<and> ns\<^sub>s \<in> q\<^sub>s" 
      using a00 a4 comm_ls unfolding sim_final_state_def by auto      
    ultimately have "snd (last l\<^sub>c) \<in> Normal ` q\<^sub>c" using  a00 a4 a3  
      unfolding sim_final_state_def ToInv_def by force
  }  
  also {
    assume a00:"(\<exists>i<length (fst (last l\<^sub>c)).  (fst (last l\<^sub>c))!i = Throw)"    
    obtain ns\<^sub>c  where  nsc:"snd (last l\<^sub>c) = Normal ns\<^sub>c" 
      using a4 a00 unfolding sim_final_state_def by auto      
    moreover obtain ns\<^sub>s where nssq:"snd (last l\<^sub>s) = Normal ns\<^sub>s \<and> ns\<^sub>s \<in> a\<^sub>s"  
      using a4 comm_ls a00 unfolding sim_final_state_def by auto     
    ultimately have "snd (last l\<^sub>c) \<in> Normal ` a\<^sub>c" using a00 a4 a3  
      unfolding sim_final_state_def ToInv_def by force
  }
  ultimately show ?thesis by auto
qed
 
  
lemma RG_SIM_fst_env_comm_ref2: 
assumes  
 a0:"(\<Gamma>\<^sub>c,(c\<^sub>c,s\<^sub>c),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,s\<^sub>s),R\<^sub>s,G\<^sub>s)" and
 a1:"\<gamma>qn = \<Down>\<^sub>i\<gamma>\<^sub>q \<and> q\<^sub>s \<subseteq> Domain \<gamma>qn \<and> ((\<gamma>qn `` q\<^sub>s) \<subseteq> q\<^sub>c) \<and>
     \<gamma>an = \<Down>\<^sub>i\<gamma>\<^sub>a \<and> a\<^sub>s \<subseteq> Domain \<gamma>an \<and> ((\<gamma>an `` a\<^sub>s)\<subseteq> a\<^sub>c)" and                  
 a2:"(\<Gamma>\<^sub>s,l\<^sub>s) \<in> par_comm\<^sub>e(G\<^sub>s, (q\<^sub>s,a\<^sub>s)) F \<and>
     (\<Gamma>\<^sub>s,l\<^sub>s)\<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and> 
     (\<Gamma>\<^sub>s,l\<^sub>s) \<in> par_assum(p\<^sub>s,R\<^sub>s) \<and> All_End (last l\<^sub>s) \<and> 
     sim_final_state (fst (last l\<^sub>c)) (snd (last l\<^sub>c)) (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a" and
 a3:"(\<Gamma>\<^sub>c,l\<^sub>c)\<in>par_cp\<^sub>e \<Gamma>\<^sub>c c\<^sub>c s\<^sub>c \<and> (\<Gamma>\<^sub>c,l\<^sub>c) \<in> par_assum(p\<^sub>c,R\<^sub>c)" and
 a4:"snd (last l\<^sub>c) \<notin> Fault ` F" 
shows "All_End (last l\<^sub>c)  \<longrightarrow>                   
          (\<exists>j<length (fst (last l\<^sub>c)). ((fst (last l\<^sub>c)!j = Throw \<and> 
            snd (last l\<^sub>c) \<in> Normal ` a\<^sub>c))) \<or>
          (\<forall>j<length (fst (last l\<^sub>c)). (fst (last l\<^sub>c)!j = Skip \<and> 
            snd (last l\<^sub>c) \<in> Normal ` q\<^sub>c))"
proof -
  {
    assume "All_End (last l\<^sub>c)"
    then have final:"(\<forall>j<length (fst (last l\<^sub>c)). fst (last l\<^sub>c)!j = Skip) \<or> 
               (\<exists>j<length (fst (last l\<^sub>c)).  fst (last l\<^sub>c)!j = Throw)"
      unfolding All_End_def final_def by fastforce        
    then have "(\<exists>j<length (fst (last l\<^sub>c)). ((fst (last l\<^sub>c)!j = Throw \<and> 
               snd (last l\<^sub>c) \<in> Normal ` a\<^sub>c))) \<or>
              (\<forall>j<length (fst (last l\<^sub>c)). (fst (last l\<^sub>c)!j = Skip \<and> 
              snd (last l\<^sub>c) \<in> Normal ` q\<^sub>c))" 
      using final a1 a2  final_c_lambda3[OF _ a4 _ _, of \<Gamma>\<^sub>s l\<^sub>s G\<^sub>s q\<^sub>s a\<^sub>s \<gamma>qn \<gamma>\<^sub>q q\<^sub>c \<gamma>an \<gamma>\<^sub>a a\<^sub>c] by blast  
  } thus ?thesis by auto
qed

lemma RG_SIM_fst_env_par_comm_ref: 
  assumes  
   a0:"(\<Gamma>\<^sub>c,(c\<^sub>c,s\<^sub>c),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,s\<^sub>s),R\<^sub>s,G\<^sub>s)" and     
   a1:"\<gamma>qn = \<Down>\<^sub>i\<gamma>\<^sub>q \<and> q\<^sub>s \<subseteq> Domain \<gamma>qn \<and> ((\<gamma>qn `` q\<^sub>s) \<subseteq> q\<^sub>c) \<and>
       \<gamma>an = \<Down>\<^sub>i\<gamma>\<^sub>a \<and> a\<^sub>s \<subseteq> Domain \<gamma>an \<and> ((\<gamma>an `` a\<^sub>s) \<subseteq> a\<^sub>c)" and                     
   a2:"(\<Gamma>\<^sub>c,l\<^sub>c)\<in>par_cp\<^sub>e \<Gamma>\<^sub>c c\<^sub>c s\<^sub>c \<and> (\<Gamma>\<^sub>c,l\<^sub>c) \<in> par_assum(p\<^sub>c,R\<^sub>c)" and
   a3:"s\<^sub>s \<in> Normal ` p\<^sub>s"  and
   a4:"\<Gamma>\<^sub>s \<Turnstile>\<^sub>e\<^bsub>/F\<^esub> c\<^sub>s SAT [p\<^sub>s, R\<^sub>s, G\<^sub>s, q\<^sub>s,a\<^sub>s]" and 
   a6:"R\<^sub>s \<subseteq> \<alpha>\<^sub>x" and a7:"R\<^sub>c \<subseteq>  in_rel (R\<^sub>s\<^sup>*) \<alpha>" and a8:"\<forall>\<Sigma>. (\<Sigma>,\<Sigma>)\<in>R\<^sub>s"
 shows "(\<Gamma>\<^sub>c,l\<^sub>c) \<in> par_comm\<^sub>e (G\<^sub>c, (q\<^sub>c,a\<^sub>c)) F"
proof-      
  {assume a01:"snd (last l\<^sub>c) \<notin> Fault ` F"
          
   {fix i e
     assume b00:"Suc i<length l\<^sub>c" and
            b01:"\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e(l\<^sub>c!i)  \<rightarrow> (l\<^sub>c!(Suc i))"
     obtain l\<^sub>s where ls:"(\<Gamma>\<^sub>s,l\<^sub>s)\<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and>
                      (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                          \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                        (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
                       (\<forall>i<length l\<^sub>c. (\<exists>i\<^sub>s<length l\<^sub>s. 
                          (\<Gamma>\<^sub>c,l\<^sub>c !i ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,l\<^sub>s!i\<^sub>s,R\<^sub>s,G\<^sub>s) )) \<and>                       
                       snd (last l\<^sub>s) \<notin> Fault ` F" 
      using RG_SIM_cp_all_sim_l\<^sub>s_fault[OF _ a0 a01 a6 a7 a8] a2 a3 unfolding par_assum_def par_cp\<^sub>e_def
      by auto
    moreover have ass:"(\<Gamma>\<^sub>s,l\<^sub>s)\<in>par_assum(p\<^sub>s,R\<^sub>s)" 
      using calculation a3 unfolding par_assum_def par_cp\<^sub>e_def by auto   
    ultimately have comm:"(\<Gamma>\<^sub>s,l\<^sub>s) \<in> par_comm\<^sub>e(G\<^sub>s, (q\<^sub>s,a\<^sub>s)) F"
      using a4 unfolding par_com_validity_def by auto            
    have ass:"(\<Gamma>\<^sub>s,l\<^sub>s)\<in>par_assum(UNIV,R\<^sub>s)" using ass 
      unfolding par_assum_def  by auto     
    then have "(snd(l\<^sub>c!i), snd(l\<^sub>c!(Suc i))) \<in> G\<^sub>c" 
      using RG_SIM_fst_env_comm_ref1[OF _ b00 b01 comm   _ _ _ ass] 
       ls  a0  a2 a01 unfolding par_cp\<^sub>e_def by blast
   } 
   then have f1:"\<forall>i e. Suc i< length l\<^sub>c \<longrightarrow> 
                    (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e(l\<^sub>c!i)  \<rightarrow> (l\<^sub>c!(Suc i))) \<longrightarrow>
                   (snd(l\<^sub>c!i), snd(l\<^sub>c!(Suc i))) \<in> G\<^sub>c" by auto   
   {
     assume a00:"All_End (last l\<^sub>c)"
     obtain l\<^sub>s where 
       "(\<Gamma>\<^sub>s,l\<^sub>s)\<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and>
        (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
             \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
             (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
         All_End (last l\<^sub>s) \<and> sim_final_state (fst (last l\<^sub>c)) (snd (last l\<^sub>c)) (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a"
       using a2 a3 RG_SIM_cp_all_sim_l\<^sub>s_All_End[OF _ a0 a00 a6 a7 a8]
       unfolding par_assum_def par_cp\<^sub>e_def by auto
     moreover then have "(\<Gamma>\<^sub>s,l\<^sub>s)\<in>par_assum(p\<^sub>s,R\<^sub>s)" using a3 unfolding par_assum_def par_cp\<^sub>e_def by auto  
     ultimately moreover have "(\<Gamma>\<^sub>s,l\<^sub>s) \<in> par_comm\<^sub>e(G\<^sub>s, (q\<^sub>s,a\<^sub>s)) F"
       using a4 unfolding par_com_validity_def by auto      
     ultimately have a4:"(\<Gamma>\<^sub>s,l\<^sub>s) \<in> par_comm\<^sub>e(G\<^sub>s, (q\<^sub>s,a\<^sub>s)) F \<and>
       (\<Gamma>\<^sub>s,l\<^sub>s)\<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and> 
       (\<Gamma>\<^sub>s,l\<^sub>s) \<in> par_assum(p\<^sub>s,R\<^sub>s) \<and> All_End (last l\<^sub>s) \<and> 
       sim_final_state (fst (last l\<^sub>c)) (snd (last l\<^sub>c)) (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a"
      by auto 
     then have "All_End (last l\<^sub>c)  \<longrightarrow>                   
          (\<exists>j<length (fst (last l\<^sub>c)). ((fst (last l\<^sub>c)!j = Throw \<and> 
            snd (last l\<^sub>c) \<in> Normal ` a\<^sub>c))) \<or>
          (\<forall>j<length (fst (last l\<^sub>c)). (fst (last l\<^sub>c)!j = Skip \<and> 
            snd (last l\<^sub>c) \<in> Normal ` q\<^sub>c))" 
      using RG_SIM_fst_env_comm_ref2[OF a0 a1 _ a2 a01] by fastforce
   }
   then have "All_End (last l\<^sub>c) \<longrightarrow>
             (\<exists>j<length (fst (last l\<^sub>c)). ((fst (last l\<^sub>c)!j = Throw \<and> 
            snd (last l\<^sub>c) \<in> Normal ` a\<^sub>c))) \<or>
          (\<forall>j<length (fst (last l\<^sub>c)). (fst (last l\<^sub>c)!j = Skip \<and> 
            snd (last l\<^sub>c) \<in> Normal ` q\<^sub>c))" by auto
   note res = conjI [OF this f1]   
  }
   thus?thesis unfolding par_comm\<^sub>e_def by auto  
 qed

definition set_to_list::"'a set \<Rightarrow> ('a list) set \<Rightarrow> ('a list) set"
  where"set_to_list s s1\<equiv>{l. \<exists>a l1. l=a#l1 \<and> a\<in>s \<and> l1\<in>s1}"


definition image_set_list_list::"('a set) list \<Rightarrow> ('a list) set"
  where
"image_set_list_list sl \<equiv> foldr (\<lambda>a l. set_to_list a l) sl {}"

definition image_list::"('s, 'ss) invs \<Rightarrow> 's list \<Rightarrow> ('ss set) list"
  where "image_list \<alpha> l  \<equiv> map (\<lambda>a. \<alpha>``{a}) l"

definition state_list_map::"('s list)set \<Rightarrow> ('s,'ss) invs \<Rightarrow> (('ss set) list) set"
  where "state_list_map s \<alpha> \<equiv> {l. \<exists>l'. l'\<in>s \<and> l = image_list \<alpha> l'}"





(* definition Refinement ::"('ss,'p,'f,'e) body \<Rightarrow> ('ss,'p,'f,'e) com list  \<Rightarrow>  ('sc,'ss)  invs \<Rightarrow>
                         ('sc,'p,'f,'e) body \<Rightarrow> ('sc,'p,'f,'e) com list  \<Rightarrow> bool" ("'(_,_') \<sqsubseteq>\<^sub>_ '(_,_')" [45, 45, 45,45, 45] 60)
  where "(\<Gamma>\<^sub>s,S) \<sqsubseteq>\<^sub>\<alpha> (\<Gamma>\<^sub>c,C) \<equiv> \<forall>\<Sigma>. (par_cp \<Gamma>\<^sub>c C (\<alpha>``\<Sigma>)) \<subseteq> (par_cp \<Gamma>\<^sub>s S \<Sigma>)" *)

   
lemma SAT_e_eq:"(\<Gamma> \<Turnstile>\<^sub>e\<^bsub>/F\<^esub> c SAT [p, R, G, q,a]) = (\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c SAT [p, R, G, q,a])" 
  unfolding par_com_validity_def LocalRG_HoareDef.par_com_validity_def   
  using eq_par_cp\<^sub>e_par_cp par_comm_eq_par_comm\<^sub>e by fast   
     
lemma RG_SIM_RG_pre: "(\<Gamma>\<^sub>c,c\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow>  
                p\<^sub>c \<subseteq> Domain \<xi> \<and>  ( \<xi> `` p\<^sub>c \<subseteq> p\<^sub>s) \<and> 
               \<gamma>qn = \<Down>\<^sub>i\<gamma>\<^sub>q \<and> q\<^sub>s \<subseteq> Domain \<gamma>qn \<and> ((\<gamma>qn `` q\<^sub>s) \<subseteq> q\<^sub>c) \<and>
                \<gamma>an = \<Down>\<^sub>i\<gamma>\<^sub>a \<and> a\<^sub>s \<subseteq> Domain \<gamma>an \<and> ((\<gamma>an `` a\<^sub>s) \<subseteq> a\<^sub>c)  \<Longrightarrow>  R\<^sub>s \<subseteq> \<alpha>\<^sub>x \<Longrightarrow> 
                R\<^sub>c \<subseteq>  in_rel (R\<^sub>s\<^sup>*) \<alpha> \<Longrightarrow> \<forall>\<Sigma>. (\<Sigma>,\<Sigma>)\<in>R\<^sub>s \<Longrightarrow>
               (\<Gamma>\<^sub>s \<Turnstile>\<^bsub>/F\<^esub> c\<^sub>s SAT [p\<^sub>s, R\<^sub>s, G\<^sub>s, q\<^sub>s,a\<^sub>s]) \<longrightarrow> (\<Gamma>\<^sub>c \<Turnstile>\<^bsub>/F\<^esub> c\<^sub>c SAT [p\<^sub>c, R\<^sub>c, G\<^sub>c, q\<^sub>c,a\<^sub>c])"  
proof -
  assume a0: "(\<Gamma>\<^sub>c,c\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s)" and         
         a1: " p\<^sub>c \<subseteq> Domain \<xi> \<and>  ( \<xi> `` p\<^sub>c \<subseteq> p\<^sub>s) \<and> 
               \<gamma>qn = \<Down>\<^sub>i\<gamma>\<^sub>q \<and> q\<^sub>s \<subseteq> Domain \<gamma>qn \<and> ((\<gamma>qn `` q\<^sub>s) \<subseteq> q\<^sub>c) \<and>
               \<gamma>an = \<Down>\<^sub>i\<gamma>\<^sub>a \<and> a\<^sub>s \<subseteq> Domain \<gamma>an \<and> ((\<gamma>an `` a\<^sub>s) \<subseteq> a\<^sub>c) " and
 a4:"R\<^sub>s \<subseteq> \<alpha>\<^sub>x" and a5:"R\<^sub>c \<subseteq>  in_rel (R\<^sub>s\<^sup>*) \<alpha>" and a6:"\<forall>\<Sigma>. (\<Sigma>,\<Sigma>)\<in>R\<^sub>s"
  {
    assume b0:"\<Gamma>\<^sub>s \<Turnstile>\<^bsub>/F\<^esub> c\<^sub>s SAT [p\<^sub>s, R\<^sub>s, G\<^sub>s, q\<^sub>s,a\<^sub>s]" 
    then have "\<Gamma>\<^sub>c \<Turnstile>\<^bsub>/F\<^esub> c\<^sub>c SAT [p\<^sub>c, R\<^sub>c, G\<^sub>c, q\<^sub>c,a\<^sub>c]"
    proof-
      {fix s\<^sub>c l
        assume c0:"l\<in> par_cp \<Gamma>\<^sub>c c\<^sub>c s\<^sub>c \<inter> par_assum(p\<^sub>c, R\<^sub>c)"
        then obtain s\<^sub>cn where sa_normal:"s\<^sub>c \<in> Normal ` p\<^sub>c \<and> s\<^sub>c = Normal s\<^sub>cn" 
          unfolding par_assum_def par_cp_def by auto   
        then obtain s\<^sub>sn where 
           sa_sa'_xi:"(s\<^sub>cn,s\<^sub>sn)\<in>\<xi>" and
           sa'_normal:"s\<^sub>sn \<in> p\<^sub>s" using a1 by force        
        have sim:"(\<Gamma>\<^sub>c,(c\<^sub>c,s\<^sub>c),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,Normal s\<^sub>sn),R\<^sub>s,G\<^sub>s)" 
          using a0 sa_sa'_xi sa_normal unfolding RGSIM_p_pre_def by auto                               
        have "l\<in>par_comm(G\<^sub>c, (q\<^sub>c,a\<^sub>c)) F" 
          using RG_SIM_fst_env_par_comm_ref[OF sim _  _ _ _ a4 a5 a6, of \<gamma>qn q\<^sub>s q\<^sub>c \<gamma>an a\<^sub>s a\<^sub>c]  c0 a1 
            b0 SAT_e_eq par_comm_eq_par_comm\<^sub>e eq_par_cp\<^sub>e_par_cp sa'_normal
          unfolding par_cp_def  by fast
      } thus ?thesis unfolding LocalRG_HoareDef.par_com_validity_def by auto
    qed      
  } thus ?thesis by auto
qed  
  
end

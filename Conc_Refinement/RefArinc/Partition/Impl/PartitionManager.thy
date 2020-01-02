theory PartitionManager1
  imports "../ArincMultiCoreState"
begin                   

lemma inter_pre_post1:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> C sat [P1, R1, G,Q1,A1] \<Longrightarrow>
       \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> C sat [P2, R2, G,Q2,A2] \<Longrightarrow> 
       \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> C sat [P1 \<inter> P2, R1 \<inter> R2, G, Q1 \<inter> Q2,A1 \<inter> A2]"
  by (simp add: Conj_post LocalRG_HoareDef.conseqPrePost)

lemma inter_pre_post:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> C sat [P1, R1, G,Q1,A1] \<Longrightarrow>
       \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> C sat [P2, R2, G,Q2,A2] \<Longrightarrow> 
       P \<subseteq> P1 \<inter> P2 \<Longrightarrow> Q1 \<inter> Q2 \<subseteq> Q \<Longrightarrow> A1 \<inter> A2 \<subseteq> A \<Longrightarrow> R \<subseteq> R1 \<inter> R2 \<Longrightarrow>
       \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> C sat [P, R, G, Q, A]"
  apply (drule inter_pre_post1) 
    apply simp apply (rule conseqPrePost)
  by auto
  

lemma Pre_union:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> C sat [P1, R, G,Q,A] \<Longrightarrow>
       \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> C sat [P2, R, G,Q,A] \<Longrightarrow> 
       \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> C sat [P1 \<union> P2, R, G, Q, A]"
 by (meson lrghoare.Conseq Un_iff order_refl)

definition Guarantee_part_set_mode
where
"Guarantee_part_set_mode i x1 y1 \<equiv>    
  let p_cur = the o partition_conf conf o current o schedule in           
    length (locals_' x1) = length (locals_' y1) \<and>   
    evnt (locals_' x1 !i) = evnt (locals_' y1 !i) \<and> 
    pt (locals_' x1 !i) =  pt (locals_' y1 !i) \<and>
    i_partition (locals_' x1!i) = i_partition (locals_' y1!i) \<and>
    in_p_mode (locals_' x1!i) = in_p_mode (locals_' y1!i) \<and>
    port_name_' (locals_' x1 !i) = port_name_' (locals_' y1 !i) \<and>
    a_que_aux (locals_' x1 !i) = a_que_aux (locals_' y1 !i) \<and> 
    r_que_aux (locals_' x1 !i) = r_que_aux (locals_' y1 !i) \<and>
    schedule (locals_' x1 !i) =  schedule (locals_' y1 !i) \<and>                  
    (\<forall>j. j\<noteq>i \<longrightarrow> (locals_' x1)!j = (locals_' y1)!j) \<and>
    timer_' x1 = timer_' y1 \<and>
    (* state_conf x1 = state_conf y1 \<and>   *)
    (* (communication_' x1) = (communication_' y1) \<and> *)               
    (part_get_mutex (partitions_' x1) (i_partition (locals_' x1!i)) \<noteq> 
     part_get_mutex (partitions_' y1) (i_partition (locals_' x1!i)) \<longrightarrow>
      (part_get_mutex (partitions_' x1) (i_partition (locals_' x1!i)) = 0 \<or> 
       part_get_mutex (partitions_' y1) (i_partition (locals_' x1!i)) = 0) \<and>
      (part_get_mutex (partitions_' x1) (i_partition (locals_' x1!i)) = i+1 \<or> 
       part_get_mutex (partitions_' y1) (i_partition (locals_' x1!i)) = i+1)) \<and> 
    (partitions_' x1 \<noteq> partitions_' y1 \<longrightarrow> 
       (part_get_mutex (partitions_' x1) (i_partition (locals_' x1!i)) = (i+1) \<or>
        part_get_mutex (partitions_' y1) (i_partition (locals_' x1!i)) = (i+1)) \<and>
        part_exists (partitions_' x1) (i_partition (locals_' x1!i)) \<and>        
       part_exists (partitions_' y1) (i_partition (locals_' x1!i)) \<and>
       ((part_mode (the (partitions_' x1  (i_partition (locals_' x1!i))))  \<noteq> 
         part_mode (the (partitions_' y1  (i_partition (locals_' x1!i)))) \<or> 
         part_restart (the (partitions_' x1  (i_partition (locals_' x1!i))))  \<noteq> 
         part_restart (the (partitions_' y1  (i_partition (locals_' x1!i))))) \<longrightarrow>        
           ((i_partition (locals_' x1!i) = (current (schedule (locals_' x1!i)))) \<or> 
            part_type (p_cur (locals_' x1!i)) = SYSTEM_PARTITION) \<and>
           part_mode (the ((partitions_' y1) (i_partition (locals_' x1!i)))) = 
             (in_p_mode (locals_' x1!i)) \<and>
           (part_mode (the (partitions_' x1  (i_partition (locals_' x1!i)))) = COLD_START \<longrightarrow>
             (in_p_mode (locals_' x1!i))\<noteq>WARM_START) \<and>
           part_restart (the ((partitions_' y1) (i_partition (locals_' x1!i)))) = 
            (in_r_mode (locals_' x1!i)))) \<and>
   (\<forall>p_id. p_id\<noteq>(i_partition (locals_' x1!i)) \<longrightarrow> 
       (partitions_' x1) p_id = (partitions_' y1) p_id)    
"   

definition Guarantee_part_get_state
where
"Guarantee_part_get_state i x1 y1 \<equiv>               
    length (locals_' x1) = length (locals_' y1) \<and>   
    evnt (locals_' x1 !i) = evnt (locals_' y1 !i) \<and> 
    pt (locals_' x1 !i) =  pt (locals_' y1 !i) \<and>
    i_partition (locals_' x1!i) = i_partition (locals_' y1!i) \<and>
    in_p_mode (locals_' x1!i) = in_p_mode (locals_' y1!i) \<and>
    port_name_' (locals_' x1 !i) = port_name_' (locals_' y1 !i) \<and>
    a_que_aux (locals_' x1 !i) = a_que_aux (locals_' y1 !i) \<and> 
    r_que_aux (locals_' x1 !i) = r_que_aux (locals_' y1 !i) \<and>
    schedule (locals_' x1 !i) =  schedule (locals_' y1 !i) \<and>                  
    (\<forall>j. j\<noteq>i \<longrightarrow> (locals_' x1)!j = (locals_' y1)!j) \<and>
    timer_' x1 = timer_' y1 \<and>
    (* state_conf x1 = state_conf y1 \<and>   *)
    (* (communication_' x1) = (communication_' y1) \<and> *)                    
       (partitions_' x1) = (partitions_' y1) 
"   


definition Rely_part_set_mode
  where
"Rely_part_set_mode i x1 y1 \<equiv>    
    ((locals_' x1)!i = (locals_' y1)!i \<and> 
     length (locals_' x1) = length (locals_' y1) \<and>     
     (\<forall>j.  (evnt (locals_' x1 !j) = evnt (locals_' y1 !j)) \<and>
            (pt (locals_' x1 !j) = pt (locals_' y1 !j)) \<and> 
            port_name_' (locals_' x1 !j) = port_name_' (locals_' y1 !j) \<and>
            a_que_aux (locals_' x1 !j) = a_que_aux (locals_' y1 !j) \<and> 
            r_que_aux (locals_' x1 !j) = r_que_aux (locals_' y1 !j) \<and>
            (evnt (locals_' x1 ! j) \<noteq> Scheduler \<longrightarrow> 
               schedule (locals_' x1 !j) =  schedule (locals_' y1 !j)) \<and>
            i_partition (locals_' x1!j) = i_partition (locals_' y1!j) \<and> 
            in_p_mode (locals_' x1!j) = in_p_mode (locals_' y1!j) ) \<and>  
     timer_' x1 = timer_' y1 \<and> 
     (\<forall>p. (part_exists (partitions_' x1) p = part_exists (partitions_' y1) p)) \<and>
     (* state_conf x1 = state_conf y1 \<and>
     (communication_' x1) = (communication_' y1) \<and> *)     
     (part_get_mutex (partitions_' x1) (i_partition (locals_' x1!i)) = i+1 \<or> 
       part_get_mutex (partitions_' y1) (i_partition (locals_' x1!i)) = i+1 \<longrightarrow> 
       (partitions_' x1) (i_partition (locals_' x1!i)) = (partitions_' y1) (i_partition (locals_' x1!i))) \<and>              
     (partitions_' x1  (i_partition (locals_' x1!i))  \<noteq> partitions_' y1  (i_partition (locals_' x1!i)) \<longrightarrow>
       (\<exists>j<procs conf. j\<noteq>i \<and> 
          (i_partition (locals_' x1!j)) = (i_partition (locals_' x1!i)) \<and>
           part_exists (partitions_' x1) (i_partition (locals_' x1!j)) \<and>          
           evnt (locals_' x1 ! j) = Set_Partition_Mode \<and>           
           ((part_mode (the (partitions_' x1  (i_partition (locals_' x1!i))))  \<noteq> 
             part_mode (the (partitions_' y1  (i_partition (locals_' x1!i)))) \<or> 
             part_restart (the (partitions_' x1  (i_partition (locals_' x1!i))))  \<noteq> 
             part_restart (the (partitions_' y1  (i_partition (locals_' x1!i))))) \<longrightarrow>  
               (i_partition (locals_' x1 ! j) = (current (schedule (locals_' x1 ! j))) \<or> 
                 part_type ((the o partition_conf conf o current o schedule) (locals_' x1!j)) = 
                 SYSTEM_PARTITION) \<and>
               part_mode (the ((partitions_' y1) (i_partition (locals_' x1!j)))) = 
                 (in_p_mode (locals_' x1!j)) \<and>
               (part_mode (the (partitions_' x1  (i_partition (locals_' x1!i)))) = COLD_START \<longrightarrow>
                 (in_p_mode (locals_' x1!j))\<noteq>WARM_START) \<and>
               part_restart (the ((partitions_' y1) (i_partition (locals_' x1!j)))) = 
                  (in_r_mode (locals_' x1!j)))))\<and>    
    (\<forall>p_id. (\<nexists>j. j<procs conf \<and> p_id =  (i_partition (locals_' x1!j))) \<longrightarrow> 
             (partitions_' x1) p_id = (partitions_' y1) p_id))
 "  

  
definition Guarantee_part
  where
"Guarantee_part i \<equiv>    
  {(x,y). (\<exists>x1 y1. 
    x=Normal x1 \<and> y = Normal y1 \<and>
      ((evnt (locals_' x1 !i) = Set_Partition_Mode \<longrightarrow> 
         Guarantee_part_set_mode i x1 y1) \<and> 
     (evnt (locals_' x1 !i) = Get_Partition_Status \<longrightarrow> Guarantee_part_get_state i x1 y1)) \<and>
     (evnt (locals_' x1 !i) \<noteq> Set_Partition_Mode \<and>
      evnt (locals_' x1 !i) \<noteq> Get_Partition_Status \<longrightarrow> x1=y1 ))
   }"

definition Rely_part
  where
"Rely_part i \<equiv>
{(x,y). (\<exists>x1 y1. 
    x=Normal x1 \<and> y = Normal y1 \<and>
    Rely_part_set_mode i x1 y1) \<or> (x=y) 
 }"

lemma Guar_Rely_Send_ReceiveQ1:
"i < n \<Longrightarrow> 
 x < n \<Longrightarrow> x \<noteq> i \<Longrightarrow> evnt (locals_' a ! x) = Set_Partition_Mode \<Longrightarrow>
 a\<noteq>b \<Longrightarrow>
 procs conf = n \<Longrightarrow>
 Guarantee_part_set_mode x a b  \<Longrightarrow> 
 Rely_part_set_mode i a b"
  unfolding Guarantee_part_set_mode_def Rely_part_set_mode_def Let_def
  apply clarify 
  apply (rule conjI)+
   apply simp
  apply (rule conjI)+
  apply (simp)
  apply (rule conjI)+
  apply (metis (mono_tags, lifting))
  apply (rule conjI)+
  apply simp
  apply (rule conjI)+
  apply (metis part_exists_def)
  apply (rule conjI)+
   apply (smt add_right_cancel less_add_same_cancel1 less_one not_less_zero)   
  by (smt add_right_cancel less_add_same_cancel1 less_one not_less_zero)

lemma h1:" i < Sys_Config.procs conf \<Longrightarrow>
       x < Sys_Config.procs conf \<Longrightarrow>
       x \<noteq> i \<Longrightarrow>
       n = Sys_Config.procs conf \<Longrightarrow>
       a = Normal x1 \<Longrightarrow>
       b = Normal y1 \<Longrightarrow>       
       Guarantee_part_get_state x x1 y1 \<Longrightarrow>
       x1 \<noteq> y1 \<Longrightarrow> evnt (locals_' x1 ! x) = Get_Partition_Status \<Longrightarrow> Rely_part_set_mode i x1 y1"
 unfolding Guarantee_part_get_state_def Rely_part_set_mode_def Let_def
  apply clarify   
  apply (rule conjI)+
   apply simp
  apply (rule conjI)+
  apply (simp)
  apply (rule conjI)+
  apply (metis (mono_tags, lifting))
  apply (rule conjI)+
  apply simp
  apply (rule conjI)+
  by auto


lemma Guar_Rely_Send_ReceiveQ:
"i < n \<Longrightarrow> 
 x < n \<Longrightarrow> x \<noteq> i \<Longrightarrow>
 procs conf = n \<Longrightarrow>
 (a, b) \<in> Guarantee_part x  \<Longrightarrow> 
 (a, b) \<in> Rely_part i"
  unfolding Guarantee_part_def Rely_part_def
  apply auto  
     apply (fastforce intro: h1)
    apply (fastforce intro: Guar_Rely_Send_ReceiveQ1)
   apply (fastforce intro: Guar_Rely_Send_ReceiveQ1)
  by (fastforce intro: h1)
  


definition get_partition_status::"nat \<Rightarrow> (vars_part,(Evnt\<times>nat),Faults,Events) com"
where
"get_partition_status i \<equiv>
    let p_cur = the o partition_conf conf o current o schedule in
   \<acute>locals :==\<^sub>E\<^sub>V \<acute>locals[i:=(\<acute>locals!i)
          \<lparr>ret_p_s := \<lparr>ps_id = current (schedule (\<acute>locals!i)),
                      ps_period = part_period (p_cur (\<acute>locals!i)),
                      ps_duration=part_duration (p_cur (\<acute>locals!i)),
                      ps_mode = part_get_mode \<acute>partitions (current (schedule (\<acute>locals!i))),
                      ps_restart = part_get_restart \<acute>partitions (current (schedule (\<acute>locals!i)))\<rparr> \<rparr>]
"

lemma exist_ret:
     " part_state_conf s \<Longrightarrow> i < length (locals_' s) \<Longrightarrow>
       part_exists (partitions_' s) (current (schedule (locals_' s!i))) \<Longrightarrow>
       \<exists>u. u = \<lparr>ps_id = current (schedule (locals_' s !i)),
                      ps_period = part_period ((the o partition_conf conf o current o schedule) (locals_' s!i)),
                      ps_duration=part_duration ((the o partition_conf conf o current o schedule) (locals_' s!i)),
                      ps_mode = part_mode (the ((partitions_' s) (current (schedule (locals_' s !i))))),
                      ps_restart = part_restart (the ((partitions_' s) (current (schedule (locals_' s !i)))))\<rparr> "
  by auto

definition set_partition_mode::"nat \<Rightarrow> (vars_part,(Evnt\<times>nat),Faults,Events) com"
where
"set_partition_mode i \<equiv> 
 (AWAIT\<^sub>\<down>\<^sub>E\<^sub>V (part_get_mutex \<acute>partitions (i_partition (\<acute>locals!i)) = 0)
     (\<acute>partitions :==\<^sub>s part_set_mutex \<acute>partitions  (i_partition (\<acute>locals!i)) (i+1))) ;;
  (AWAIT\<^sub>\<down>\<^sub>E\<^sub>V True
   ((IF\<^sub>s (part_mode (the (\<acute>partitions  (i_partition (\<acute>locals!i)))) = COLD_START) \<and>
       in_p_mode (\<acute>locals!i) = WARM_START THEN
        \<acute>locals :==\<^sub>s \<acute>locals[i:=(\<acute>locals!i)\<lparr>ret_n := 0 \<rparr>]    
      ELSE
        \<acute>partitions :==\<^sub>s part_set_mode \<acute>partitions (i_partition (\<acute>locals!i)) (in_p_mode (\<acute>locals!i));;\<^sub>s
        \<acute>partitions :==\<^sub>s part_set_restart \<acute>partitions  (i_partition (\<acute>locals!i)) (in_r_mode (\<acute>locals!i));;\<^sub>s         
        \<acute>locals :==\<^sub>s \<acute>locals[i:=(\<acute>locals!i)\<lparr>ret_n := 1 \<rparr>]        
    FI);;\<^sub>s 
    (\<acute>partitions :==\<^sub>s part_set_mutex \<acute>partitions   (i_partition (\<acute>locals!i)) 0))) 
"



definition set_partition_mode_system::"nat \<Rightarrow> (vars_part,(Evnt\<times>nat),Faults,Events) com"
where
"set_partition_mode_system i \<equiv> 
let p_cur = the o partition_conf conf o current o schedule in
 IF part_exists \<acute>partitions (i_partition (\<acute>locals!i)) \<and> 
   ((i_partition (\<acute>locals!i) = (current (schedule (\<acute>locals!i)))) \<or> 
     part_type (p_cur (\<acute>locals!i)) = SYSTEM_PARTITION) THEN
   (set_partition_mode i)
 ELSE 
   \<acute>locals :==\<^sub>E\<^sub>V \<acute>locals[i:=(\<acute>locals!i)\<lparr>ret_n := 0 \<rparr>]       
 FI
"

 
primrec events::"Evnt \<Rightarrow> nat \<Rightarrow> (vars_part,(Evnt\<times>nat),Faults,Events) com"
where 
"events Get_Partition_Status  m = (get_partition_status m)"
|"events Set_Partition_Mode m = (set_partition_mode_system m)"


subsection {* mapping from parameterized event to list *}


definition execute_service :: "nat \<Rightarrow> (vars_part,(Evnt\<times>nat),Faults,Events) com"
where
"execute_service i \<equiv> 
  IF evnt ((\<acute>locals)!i) = Get_Partition_Status  THEN    
     Call (Get_Partition_Status,i)
  ELSE IF evnt ((\<acute>locals)!i) = Set_Partition_Mode  THEN    
     Call (Set_Partition_Mode,i)  
  FI
FI
"  
  
definition \<Gamma> :: " (Evnt\<times>nat) \<Rightarrow> ((vars_part,(Evnt\<times>nat),Faults,Events) com) option"
where
"
\<Gamma> \<equiv> (\<lambda> (s,m). if (m<procs conf) then Some (events s m) else None)
"
named_theorems body
lemma body_get_status[body]:"i < procs conf \<Longrightarrow>  \<Gamma> (Get_Partition_Status,i) = Some (get_partition_status i)"
  unfolding \<Gamma>_def by auto
    
lemma body_set_status[body]:"i < procs conf \<Longrightarrow>  \<Gamma> (Set_Partition_Mode,i) = Some (set_partition_mode_system i)"
  unfolding \<Gamma>_def by auto
 
lemma reflexive_Guarantee_Part:
  "  (Normal s, Normal s) \<in> Guarantee_part i"
  unfolding Guarantee_part_def Guarantee_part_set_mode_def Guarantee_part_get_state_def
  by auto

named_theorems pres

lemma Sta_part_state_conf_Rely_Part[pres]:
      "Sta {s. part_state_conf s} (Rely_part i)"
  unfolding Sta_def Rely_part_def Rely_part_set_mode_def part_state_conf_def part_exists_def
  by fastforce


lemma IF_1_true[pres]: "Sta \<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals!i)) \<and> 
   ((i_partition (\<acute>locals!i) = (current (schedule (\<acute>locals!i)))) \<or> 
     part_type (p_cur (\<acute>locals!i)) = SYSTEM_PARTITION)\<rbrace> (Rely_part i)" 
apply (simp add: Sta_def) 
  apply (simp add: Rely_part_def Rely_part_set_mode_def)  
  by metis

lemma IF_1_false[pres]: "Sta (-\<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals!i)) \<and> 
   ((i_partition (\<acute>locals!i) = (current (schedule (\<acute>locals!i)))) \<or> 
     part_type (p_cur (\<acute>locals!i)) = SYSTEM_PARTITION)\<rbrace>) (Rely_part i)" 
apply (simp add: Sta_def) 
  apply (simp add: Rely_part_def Rely_part_set_mode_def)  
  by metis

lemma sta_part_get_mutex[pres]: 
 "Sta \<lbrace>part_get_mutex \<acute>partitions (i_partition (\<acute>locals ! i)) = Suc i\<rbrace> (Rely_part i)"
 unfolding Sta_def Rely_part_def Rely_part_set_mode_def part_get_mutex_def
  by auto
  
lemma Sta_univ_Rely_Part[pres]: "LocalRG_HoareDef.Sta UNIV (Rely_part i)" 
  unfolding Sta_def Rely_part_def Rely_part_set_mode_def 
  by blast

lemma Sta_false[pres]: "LocalRG_HoareDef.Sta {} (Rely_part i)"
  unfolding Sta_def Rely_part_def Rely_part_set_mode_def 
  by blast
(* Stability of the Pre-condition for the equality of the partition attributes *)

lemma Sta_ipart[pres]: "Sta \<lbrace>i_partition (\<acute>locals!i) = p\<rbrace> (Rely_part i)"
apply (simp add: Sta_def) 
  apply (simp add: Rely_part_def Rely_part_set_mode_def)  
  by metis

lemma Sta_evnt[pres]: "Sta \<lbrace>evnt (\<acute>locals !i) = e\<rbrace> (Rely_part i)"
apply (simp add: Sta_def) 
  apply (simp add: Rely_part_def Rely_part_set_mode_def)  
  by metis

lemma Sta_p_mode[pres]: "Sta \<lbrace>in_p_mode (\<acute>locals!i) = m\<rbrace> (Rely_part i)"
apply (simp add: Sta_def) 
  apply (simp add: Rely_part_def Rely_part_set_mode_def)  
  by metis

lemma Sta_not_ipart[pres]: "Sta \<lbrace>i_partition (\<acute>locals!i) \<noteq> p\<rbrace> (Rely_part i)"
apply (simp add: Sta_def) 
  apply (simp add: Rely_part_def Rely_part_set_mode_def)  
  by metis

lemma Sta_not_evnt[pres]: "Sta \<lbrace>evnt (\<acute>locals !i) \<noteq> e\<rbrace> (Rely_part i)"
apply (simp add: Sta_def) 
  apply (simp add: Rely_part_def Rely_part_set_mode_def)  
  by metis

lemma Sta_not_evnt1[pres]:"LocalRG_HoareDef.Sta (- \<lbrace>evnt (\<acute>locals ! i) = n\<rbrace>) (Rely_part i)"
apply (simp add: Sta_def) 
  apply (simp add: Rely_part_def Rely_part_set_mode_def)  
  by metis

lemma Sta_not_p_mode[pres]: "Sta \<lbrace>in_p_mode (\<acute>locals!i) \<noteq> m\<rbrace> (Rely_part i)"
apply (simp add: Sta_def) 
  apply (simp add: Rely_part_def Rely_part_set_mode_def)  
  by metis


lemma set_partition_mode_eq_p_mode:
  "i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> set_partition_mode_system i sat [
            {s. part_state_conf s} \<inter> \<lbrace>evnt (\<acute>locals !i) = Set_Partition_Mode\<rbrace> \<inter> \<lbrace>in_p_mode (\<acute>locals!i) = m\<rbrace>,  
            Rely_part i, 
            Guarantee_part  i, 
            {s. part_state_conf s} \<inter> \<lbrace>evnt (\<acute>locals !i) = Set_Partition_Mode\<rbrace> \<inter> \<lbrace>in_p_mode (\<acute>locals!i) = m\<rbrace>,UNIV]"
  unfolding set_partition_mode_system_def set_partition_mode_def Let_def    
  apply (rule If, auto simp add: reflexive_Guarantee_Part)
    apply (fastforce intro: Sta_intro pres)+ 
   apply (rule Seq[of  _ _ _ _ _ _ _ _ "{s. part_state_conf s} \<inter> 
                                    \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>
                                    \<lbrace>in_p_mode (\<acute>locals ! i) = m\<rbrace> \<inter>
                                    \<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals ! i)) \<and>
                                     (i_partition (\<acute>locals ! i) = current (schedule (\<acute>locals ! i)) \<or>
                                      part_type
                                       (the (partition_conf conf (current (schedule (\<acute>locals ! i))))) =
                                      SYSTEM_PARTITION)\<rbrace> \<inter> 
                             \<lbrace>part_get_mutex \<acute>partitions (i_partition (\<acute>locals ! i)) = (Suc i)\<rbrace>"], 
             auto simp add: reflexive_Guarantee_Part)   
      apply (rule Sta_univ_Rely_Part) 
  apply (fastforce intro: Sta_intro pres)+                        
    apply (rule Await) 
  apply (fastforce intro: Sta_intro pres)+      
    apply vcg apply (auto simp add: Guarantee_part_def Guarantee_part_set_mode_def part_state_conf_def 
                     current_def part_exists_def part_get_mutex_def part_set_mutex_def)[1]
apply (rule Await) apply (fastforce intro: Sta_intro pres)+
   apply vcg apply simp
   apply (force simp add: part_set_restart_def Guarantee_part_def Guarantee_part_set_mode_def part_state_conf_def 
                     part_set_mode_def Let_def current_def part_exists_def part_get_mutex_def part_set_mutex_def)[1]
  apply (rule Basic)
     apply (fastforce intro: Sta_intro pres)+       
  by (auto simp add: Guarantee_part_def Guarantee_part_set_mode_def part_state_conf_def)

lemma set_partition_mode_not_eq_p_mode:
  "i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> set_partition_mode_system i sat [
            {s. part_state_conf s} \<inter> \<lbrace>evnt (\<acute>locals !i) = Set_Partition_Mode\<rbrace> \<inter> \<lbrace>in_p_mode (\<acute>locals!i) \<noteq> m\<rbrace>,  
            Rely_part i, 
            Guarantee_part  i, 
            {s. part_state_conf s} \<inter> \<lbrace>evnt (\<acute>locals !i) = Set_Partition_Mode\<rbrace> \<inter> \<lbrace>in_p_mode (\<acute>locals!i) \<noteq> m\<rbrace>,UNIV]"
  unfolding set_partition_mode_system_def set_partition_mode_def Let_def    
  apply (rule If, auto simp add: reflexive_Guarantee_Part)
    apply (fastforce intro: Sta_intro pres)+ 
   apply (rule Seq[of  _ _ _ _ _ _ _ _ "{s. part_state_conf s} \<inter> 
                                    \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>
                                    \<lbrace>in_p_mode (\<acute>locals ! i) \<noteq> m\<rbrace> \<inter>
                                    \<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals ! i)) \<and>
                                     (i_partition (\<acute>locals ! i) = current (schedule (\<acute>locals ! i)) \<or>
                                      part_type
                                       (the (partition_conf conf (current (schedule (\<acute>locals ! i))))) =
                                      SYSTEM_PARTITION)\<rbrace> \<inter> 
                             \<lbrace>part_get_mutex \<acute>partitions (i_partition (\<acute>locals ! i)) = (Suc i)\<rbrace>"], 
             auto simp add: reflexive_Guarantee_Part)   
      apply (rule Sta_univ_Rely_Part) 
  apply (fastforce intro: Sta_intro pres)+                        
    apply (rule Await) 
  apply (fastforce intro: Sta_intro pres)+      
    apply vcg apply (auto simp add: Guarantee_part_def Guarantee_part_set_mode_def part_state_conf_def 
                     current_def part_exists_def part_get_mutex_def part_set_mutex_def)[1]
apply (rule Await) apply (fastforce intro: Sta_intro pres)+
   apply vcg apply simp
   apply (force simp add: part_set_restart_def Guarantee_part_def Guarantee_part_set_mode_def part_state_conf_def 
                     part_set_mode_def Let_def current_def part_exists_def part_get_mutex_def part_set_mutex_def)[1]
  apply (rule Basic)
     apply (fastforce intro: Sta_intro pres)+       
  by (auto simp add: Guarantee_part_def Guarantee_part_set_mode_def part_state_conf_def)


lemma set_partition_mode_in_part:
  "i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> set_partition_mode_system i sat [
            {s. part_state_conf s} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter> 
           \<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals!i)) \<and> 
            (i_partition (\<acute>locals ! i) = current (schedule (\<acute>locals ! i)) \<or>
             part_type (the (partition_conf conf (current (schedule (\<acute>locals ! i))))) = SYSTEM_PARTITION)\<rbrace>,  
            Rely_part i, 
            Guarantee_part  i, 
            {s. part_state_conf s} \<inter> \<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals!i)) \<and> 
         (i_partition (\<acute>locals ! i) = current (schedule (\<acute>locals ! i)) \<or>
          part_type (the (partition_conf conf (current (schedule (\<acute>locals ! i))))) = SYSTEM_PARTITION)\<rbrace>,UNIV]"
  unfolding set_partition_mode_system_def set_partition_mode_def Let_def    
  apply (rule If, auto simp add: reflexive_Guarantee_Part)
    apply (fastforce intro: Sta_intro pres)+ 
   apply (rule Seq[of  _ _ _ _ _ _ _ _ "Collect part_state_conf \<inter> \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>
                                    \<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals ! i)) \<and>
                                     (i_partition (\<acute>locals ! i) = current (schedule (\<acute>locals ! i)) \<or>
                                      part_type
                                       (the (partition_conf conf (current (schedule (\<acute>locals ! i))))) =
                                      SYSTEM_PARTITION)\<rbrace> \<inter> 
                             \<lbrace>part_get_mutex \<acute>partitions (i_partition (\<acute>locals ! i)) = (Suc i)\<rbrace>"], 
             auto simp add: reflexive_Guarantee_Part)   
      apply (rule Sta_univ_Rely_Part) 
  apply (fastforce intro: Sta_intro pres)+                        
    apply (rule Await) 
  apply (fastforce intro: Sta_intro pres)+      
    apply vcg apply (auto simp add: Guarantee_part_def Guarantee_part_set_mode_def part_state_conf_def 
                     current_def part_exists_def part_get_mutex_def part_set_mutex_def)[1]
apply (rule Await) apply (fastforce intro: Sta_intro pres)+
   apply vcg apply simp
   apply (force simp add: part_set_restart_def Guarantee_part_def Guarantee_part_set_mode_def part_state_conf_def 
                     part_set_mode_def Let_def current_def part_exists_def part_get_mutex_def part_set_mutex_def)[1]
  apply (rule Basic)
  by (fastforce intro: Sta_intro pres)+       
 

lemma set_partition_mode_eq_i_partition:
  "i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> set_partition_mode_system i sat [
            {s. part_state_conf s} \<inter> \<lbrace>i_partition (\<acute>locals!i) = p\<rbrace> \<inter> \<lbrace>evnt (\<acute>locals !i) = Set_Partition_Mode\<rbrace>,  
            Rely_part i, 
            Guarantee_part  i, 
            {s. part_state_conf s} \<inter> \<lbrace>i_partition (\<acute>locals!i) = p\<rbrace> \<inter> \<lbrace>evnt (\<acute>locals !i) = Set_Partition_Mode\<rbrace>,UNIV]"
  unfolding set_partition_mode_system_def set_partition_mode_def Let_def    
  apply (rule If, auto simp add: reflexive_Guarantee_Part)
    apply (fastforce intro: Sta_intro pres)+ 
   apply (rule Seq[of  _ _ _ _ _ _ _ _ "{s. part_state_conf s} \<inter> \<lbrace>i_partition (\<acute>locals ! i) = p\<rbrace> \<inter>
                                    \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>                                    
                                    \<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals ! i)) \<and>
                                     (i_partition (\<acute>locals ! i) = current (schedule (\<acute>locals ! i)) \<or>
                                      part_type
                                       (the (partition_conf conf (current (schedule (\<acute>locals ! i))))) =
                                      SYSTEM_PARTITION)\<rbrace> \<inter> 
                             \<lbrace>part_get_mutex \<acute>partitions (i_partition (\<acute>locals ! i)) = (Suc i)\<rbrace>"], 
             auto simp add: reflexive_Guarantee_Part)   
      apply (rule Sta_univ_Rely_Part) 
  apply (fastforce intro: Sta_intro pres)+                        
    apply (rule Await) 
  apply (fastforce intro: Sta_intro pres)+      
    apply vcg apply (auto simp add: Guarantee_part_def Guarantee_part_set_mode_def part_state_conf_def 
                     current_def part_exists_def part_get_mutex_def part_set_mutex_def)[1]
apply (rule Await) apply (fastforce intro: Sta_intro pres)+
   apply vcg apply simp
   apply (force simp add: part_set_restart_def Guarantee_part_def Guarantee_part_set_mode_def part_state_conf_def 
                     part_set_mode_def Let_def current_def part_exists_def part_get_mutex_def part_set_mutex_def)[1]
  apply (rule Basic)
     apply (fastforce intro: Sta_intro pres)+       
  by (auto simp add: Guarantee_part_def Guarantee_part_set_mode_def part_state_conf_def)



lemma set_partition_mode_locals:
"i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> set_partition_mode_system i sat [
            {s. part_state_conf s} \<inter> \<lbrace>i_partition (\<acute>locals!i) = p\<rbrace> \<inter> \<lbrace>evnt (\<acute>locals !i) = Set_Partition_Mode\<rbrace> \<inter>
            \<lbrace>in_p_mode (\<acute>locals!i) \<noteq> m\<rbrace>,  
            Rely_part i, 
            Guarantee_part  i, 
            {s. part_state_conf s} \<inter> \<lbrace>i_partition (\<acute>locals!i) = p\<rbrace> \<inter> \<lbrace>evnt (\<acute>locals !i) = Set_Partition_Mode\<rbrace> \<inter>
            \<lbrace>in_p_mode (\<acute>locals!i) \<noteq> m\<rbrace>,UNIV]"  
  by (force intro: inter_pre_post  set_partition_mode_not_eq_p_mode set_partition_mode_eq_i_partition)

lemma set_partition_mode_locals1:
"i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> set_partition_mode_system i sat [
            {s. part_state_conf s} \<inter> \<lbrace>i_partition (\<acute>locals!i) = p\<rbrace> \<inter> \<lbrace>evnt (\<acute>locals !i) = Set_Partition_Mode\<rbrace> \<inter>
            \<lbrace>in_p_mode (\<acute>locals!i) \<noteq> m\<rbrace> \<inter> \<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals!i)) \<and> 
            (i_partition (\<acute>locals ! i) = current (schedule (\<acute>locals ! i)) \<or>
             part_type (the (partition_conf conf (current (schedule (\<acute>locals ! i))))) = SYSTEM_PARTITION)\<rbrace>,  
            Rely_part i, 
            Guarantee_part  i, 
            {s. part_state_conf s} \<inter> \<lbrace>i_partition (\<acute>locals!i) = p\<rbrace> \<inter> \<lbrace>evnt (\<acute>locals !i) = Set_Partition_Mode\<rbrace> \<inter>
            \<lbrace>in_p_mode (\<acute>locals!i) \<noteq> m\<rbrace>\<inter>\<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals!i)) \<and> 
            (i_partition (\<acute>locals ! i) = current (schedule (\<acute>locals ! i)) \<or>
             part_type (the (partition_conf conf (current (schedule (\<acute>locals ! i))))) = SYSTEM_PARTITION)\<rbrace>,UNIV]"      
  by (auto intro: inter_pre_post[OF set_partition_mode_locals set_partition_mode_in_part])

lemma set_partition_mode_locals'':
"i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> set_partition_mode_system i sat [
            {s. part_state_conf s} \<inter> \<lbrace>i_partition (\<acute>locals!i) = p\<rbrace> \<inter> \<lbrace>evnt (\<acute>locals !i) = Set_Partition_Mode\<rbrace> \<inter>
            \<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals!i)) \<and> 
            (i_partition (\<acute>locals ! i) = current (schedule (\<acute>locals ! i)) \<or>
             part_type (the (partition_conf conf (current (schedule (\<acute>locals ! i))))) = SYSTEM_PARTITION)\<rbrace>,  
            Rely_part i, 
            Guarantee_part  i, 
            {s. part_state_conf s} \<inter> \<lbrace>i_partition (\<acute>locals!i) = p\<rbrace> \<inter> \<lbrace>evnt (\<acute>locals !i) = Set_Partition_Mode\<rbrace> \<inter>
            \<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals!i)) \<and> 
            (i_partition (\<acute>locals ! i) = current (schedule (\<acute>locals ! i)) \<or>
             part_type (the (partition_conf conf (current (schedule (\<acute>locals ! i))))) = SYSTEM_PARTITION)\<rbrace>,UNIV]"      
  by (auto intro: inter_pre_post[OF set_partition_mode_eq_i_partition set_partition_mode_in_part])

lemma Sta_no_cond[pres]: "Sta \<lbrace>\<not>(i_partition (\<acute>locals ! i) = p \<and>        
        (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION) \<and>
        in_p_mode (\<acute>locals ! i) \<noteq> WARM_START)\<rbrace> (Rely_part i)"
apply (simp add: Sta_def) 
  apply (simp add: Rely_part_def Rely_part_set_mode_def)  
  by metis

lemma Sta_no_cond2[pres]: "
   Sta \<lbrace>\<not>(i_partition (\<acute>locals ! i) = p \<and>
        evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
        (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION) \<and>
        in_p_mode (\<acute>locals ! i) \<noteq> WARM_START)\<rbrace> (Rely_part i)"
apply (simp add: Sta_def) 
  apply (simp add: Rely_part_def Rely_part_set_mode_def)  
  by metis

(* Stability of the Pre-condition for modification of a partition in cold state*)
lemma Sta_cond_part_exists[pres]:"
    LocalRG_HoareDef.Sta
     \<lbrace>part_exists \<acute>partitions p\<rbrace>
     (Rely_part i)"
  unfolding Sta_def  Rely_part_def  Rely_part_set_mode_def  
  by fastforce

lemma Sta_cond1a[pres]:"    
    LocalRG_HoareDef.Sta
     \<lbrace> (\<exists>j<Sys_Config.procs conf.
           evnt (\<acute>locals ! j) = Set_Partition_Mode \<and> 
          p = i_partition (\<acute>locals ! j) \<and>
           in_p_mode (\<acute>locals ! j) \<noteq> WARM_START \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION))\<rbrace>
     (Rely_part i)"
  apply (simp add: Sta_def) apply clarsimp apply (erule disjE)
  apply (simp add: Rely_part_def)  
   apply (erule disjE)
    apply (erule exE)  
    apply (simp add: Rely_part_set_mode_def)    
  apply (case_tac "part_mode (the (partitions_' x' (current (schedule (locals_' x' ! j))))) \<noteq>
       part_mode (the (partitions_' y1 (current (schedule (locals_' x' ! j)))))")
     apply metis
    apply metis 
   apply fastforce 
  apply (simp add: Rely_part_def)  
  apply (erule disjE)
   apply (erule exE)
   apply (auto simp add: Rely_part_set_mode_def)[1] 
  by fastforce



lemma Sta_cond1'[pres]:"    
    LocalRG_HoareDef.Sta
     \<lbrace>i_partition (\<acute>locals ! i) = p \<and>
      (part_mode (the (p\<rightarrow>\<acute>partitions)) = COLD_START \<or>
        (\<exists>j<Sys_Config.procs conf.
            evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
            p = i_partition (\<acute>locals ! j) \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION) \<and>
          part_mode (the (p\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j)))\<rbrace>
     (Rely_part i)" 
  apply (simp add: Sta_def) apply clarsimp 
  apply auto
  apply (simp add: Rely_part_def)
     apply (erule disjE)
     apply (erule exE)
     apply (auto simp add: Rely_part_set_mode_def)[1]
    apply fastforce 
  apply (simp add: Rely_part_def)
     apply (erule disjE)
    apply (erule exE)
    apply (simp add: Rely_part_set_mode_def)  
     apply (auto simp add: Rely_part_set_mode_def)[1]
   apply fastforce 
apply (simp add: Rely_part_def)
     apply (erule disjE)
    apply (erule exE)
apply (simp add: Rely_part_set_mode_def)  
     apply (auto simp add: Rely_part_set_mode_def)[1]
  by fastforce 


lemma set_mutex_guarantee:
     " evnt (l ! i) = Set_Partition_Mode \<Longrightarrow>       
       part_get_mutex p (i_partition (l ! i)) = 0 \<Longrightarrow> 
       part_exists p (i_partition (l ! i)) \<Longrightarrow>       
       (Normal \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr>,
        Normal
         \<lparr>locals_' = l, timer_' = t,
            partitions_' = part_set_mutex p (i_partition (l ! i)) (Suc i)\<rparr>)
       \<in> Guarantee_part i"
  unfolding Guarantee_part_def Guarantee_part_set_mode_def part_set_mutex_def part_get_mutex_def
 part_exists_def current_def
  by auto

lemma set_v_guarantee:" i < Sys_Config.procs conf \<Longrightarrow>
       part_state_conf \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr> \<Longrightarrow>
       evnt (l ! i) = Set_Partition_Mode \<Longrightarrow> 
       part_exists p (i_partition (l ! i)) \<Longrightarrow>         
       part_get_mutex p (i_partition (l ! i)) = Suc i \<Longrightarrow>
        (Normal \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr>,
         Normal
          \<lparr>locals_' = l[i := (l ! i)\<lparr>ret_n := 0\<rparr>], timer_' = t,
             partitions_' =
               part_set_mutex p (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i)) 0\<rparr>)
        \<in> Guarantee_part i 
        "
unfolding Guarantee_part_def Guarantee_part_set_mode_def part_set_mutex_def part_get_mutex_def
 part_exists_def current_def part_state_conf_def
  by auto

lemma set_v_guarantee':"i < Sys_Config.procs conf \<Longrightarrow>
         part_state_conf \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr> \<Longrightarrow>
         evnt (l ! i) = Set_Partition_Mode \<Longrightarrow>         
         part_exists p (i_partition (l ! i)) \<Longrightarrow>
         i_partition (l ! i) = current (schedule (l ! i)) \<or>
         part_type (the (partition_conf conf (current (schedule (l ! i))))) = SYSTEM_PARTITION \<Longrightarrow>
         part_get_mutex p (i_partition (l ! i)) = Suc i \<Longrightarrow>
         part_mode (the (p (i_partition (l ! i)))) = COLD_START \<longrightarrow> in_p_mode (l ! i) \<noteq> WARM_START \<Longrightarrow>
         (Normal \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr>,
          Normal
           \<lparr>locals_' = l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>], timer_' = t,
              partitions_' =
                part_set_mutex
                 (part_set_restart (part_set_mode p (i_partition (l ! i)) (in_p_mode (l ! i)))
                   (i_partition (l ! i)) (in_r_mode (l ! i)))
                 (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0\<rparr>)
         \<in> Guarantee_part i "
unfolding Guarantee_part_def Guarantee_part_set_mode_def part_set_mutex_def part_get_mutex_def
 part_exists_def current_def part_state_conf_def part_set_restart_def part_set_mode_def
  by auto

lemma set_mutex_part_state_conf:"i < Sys_Config.procs conf \<Longrightarrow>
       part_state_conf \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr> \<Longrightarrow>       
       part_exists p (i_partition (l ! i)) \<Longrightarrow>
       part_state_conf
        \<lparr>locals_' = l, timer_' = t,
           partitions_' = part_set_mutex p (i_partition (l ! i)) (Suc i)\<rparr>"
  unfolding part_state_conf_def part_set_mutex_def part_get_mutex_def part_exists_def
  by auto

lemma exec:"i < Sys_Config.procs conf \<Longrightarrow>
       part_state_conf \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr> \<Longrightarrow>
       evnt (l ! i) = Set_Partition_Mode \<Longrightarrow>
       part_exists p (i_partition (l ! i)) \<Longrightarrow>
       (i_partition (l ! i) = current (schedule (l ! i)) \<or>
          part_type (the (partition_conf conf (current (schedule (l ! i))))) = SYSTEM_PARTITION) \<Longrightarrow>
       part_mode (the (p (i_partition (l ! i)))) = COLD_START \<or>
       (\<exists>j<Sys_Config.procs conf.
           evnt (l ! j) = Set_Partition_Mode \<and>
           i_partition (l ! i) = i_partition (l ! j) \<and>
           (i_partition (l ! j) = current (schedule (l ! j)) \<or>
            part_type (the (partition_conf conf (current (schedule (l ! j))))) = SYSTEM_PARTITION) \<and>
           part_mode (the (p (i_partition (l ! i)))) = in_p_mode (l ! j)) \<Longrightarrow>
       \<exists>j<Sys_Config.procs conf.
          evnt (l ! j) = Set_Partition_Mode \<and>
          i_partition (l ! i) = i_partition (l ! j) \<and>
          in_p_mode (l! j) \<noteq> WARM_START \<and>
          (i_partition (l ! j) = current (schedule (l ! j)) \<or>
           part_type (the (partition_conf conf (current (schedule (l ! j))))) = SYSTEM_PARTITION) \<Longrightarrow>
       part_exists p (i_partition (l ! i)) \<Longrightarrow>
       i_partition (l ! i) = current (schedule (l ! i)) \<or>
       part_type (the (partition_conf conf (current (schedule (l ! i))))) = SYSTEM_PARTITION \<Longrightarrow>
       part_get_mutex p (i_partition (l ! i)) = 0 \<Longrightarrow>
       (Normal \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr>,
        Normal
         \<lparr>locals_' = l, timer_' = t,
            partitions_' = part_set_mutex p (i_partition (l ! i)) (Suc i)\<rparr>)
       \<in> Guarantee_part i \<and>
       part_state_conf
        \<lparr>locals_' = l, timer_' = t,
           partitions_' = part_set_mutex p (i_partition (l ! i)) (Suc i)\<rparr> \<and>
       part_exists (part_set_mutex p (i_partition (l ! i)) (Suc i)) (i_partition (l ! i)) \<and>
       (part_mode
         (the (part_set_mutex p (i_partition (l ! i)) (Suc i) (i_partition (l ! i)))) =
        COLD_START \<or>
        (\<exists>j<Sys_Config.procs conf.
            evnt (l ! j) = Set_Partition_Mode \<and>
            i_partition (l ! i) = i_partition (l ! j) \<and>
            (i_partition (l ! j) = current (schedule (l ! j)) \<or>
             part_type (the (partition_conf conf (current (schedule (l ! j))))) = SYSTEM_PARTITION) \<and>
            part_mode
             (the (part_set_mutex p (i_partition (l ! i)) (Suc i) (i_partition (l ! i)))) =
            in_p_mode (l ! j))) \<and>
       part_exists (part_set_mutex p (i_partition (l ! i)) (Suc i)) (i_partition (l ! i)) \<and>
       part_get_mutex (part_set_mutex p (i_partition (l ! i)) (Suc i))
        (i_partition (l ! i)) =
       Suc i" using set_mutex_guarantee set_mutex_part_state_conf 
  apply auto
  unfolding part_exists_def part_set_mutex_def part_get_mutex_def  apply auto 
  by (metis option.sel)+

lemma exec1:" i < Sys_Config.procs conf \<Longrightarrow>
       part_state_conf \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr> \<Longrightarrow>
       evnt (l ! i) = Set_Partition_Mode \<Longrightarrow>
       part_mode (the (p (i_partition (l ! i)))) = COLD_START \<or>
       (\<exists>j<Sys_Config.procs conf.
           evnt (l ! j) = Set_Partition_Mode \<and>
           i_partition (l ! i) = i_partition (l ! j) \<and>
           (i_partition (l ! j) = current (schedule (l ! j)) \<or>
            part_type (the (partition_conf conf (current (schedule (l ! j))))) = SYSTEM_PARTITION) \<and>
           part_mode (the (p (i_partition (l ! i)))) = in_p_mode (l ! j)) \<Longrightarrow>
       \<exists>j<Sys_Config.procs conf.
          evnt (l ! j) = Set_Partition_Mode \<and>
          i_partition (l ! i) = i_partition (l ! j) \<and>
          in_p_mode (l ! j) \<noteq> WARM_START \<and>
          (i_partition (l ! j) = current (schedule (l ! j)) \<or>
           part_type (the (partition_conf conf (current (schedule (l ! j))))) = SYSTEM_PARTITION) \<Longrightarrow>
       part_exists p (i_partition (l ! i)) \<Longrightarrow>
       i_partition (l ! i) = current (schedule (l ! i)) \<or> part_type (the (partition_conf conf (current (schedule (l ! i))))) = SYSTEM_PARTITION \<Longrightarrow>
       part_get_mutex p (i_partition (l ! i)) = Suc i \<Longrightarrow>
       (part_mode (the (p (i_partition (l ! i)))) = COLD_START \<and> in_p_mode (l ! i) = WARM_START \<longrightarrow>
        (Normal \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr>,
         Normal \<lparr>locals_' = l[i := (l ! i)\<lparr>ret_n := 0\<rparr>], timer_' = t,
                   partitions_' = part_set_mutex p (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i)) 0\<rparr>)
        \<in> Guarantee_part i \<and>
        part_exists (part_set_mutex p (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i)) 0) (i_partition (l ! i)) \<and>
        i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i) = i_partition (l ! i) \<and>
        (part_mode (the (part_set_mutex p (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i)) 0 (i_partition (l ! i)))) = COLD_START \<or>
         (\<exists>j<Sys_Config.procs conf.
             evnt (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j) = Set_Partition_Mode \<and>
             i_partition (l ! i) =  i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j) \<and>
             (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j) = current (schedule (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j)) \<or>
              part_type (the (partition_conf conf (current (schedule (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j))))) = SYSTEM_PARTITION) \<and>
             part_mode (the (part_set_mutex p (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i)) 0 (i_partition (l ! i)))) =
             in_p_mode (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j)))) \<and>
       ((part_mode (the (p (i_partition (l ! i)))) = COLD_START \<longrightarrow> in_p_mode (l ! i) \<noteq> WARM_START) \<longrightarrow>
        (Normal \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr>,
         Normal \<lparr>locals_' = l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>], timer_' = t,
                   partitions_' =
                     part_set_mutex
                      (part_set_restart (part_set_mode p (i_partition (l ! i)) (in_p_mode (l ! i))) (i_partition (l ! i))
                        (in_r_mode (l ! i)))
                      (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0\<rparr>)
        \<in> Guarantee_part i \<and>
        part_exists
         (part_set_mutex
           (part_set_restart (part_set_mode p (i_partition (l ! i)) (in_p_mode (l ! i))) (i_partition (l ! i)) (in_r_mode (l ! i)))
           (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0)
         (i_partition (l ! i)) \<and>
        i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i) = i_partition (l ! i) \<and>
        (part_mode
          (the (part_set_mutex
                 (part_set_restart (part_set_mode p (i_partition (l ! i)) (in_p_mode (l ! i))) (i_partition (l ! i))
                   (in_r_mode (l ! i)))
                 (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0 (i_partition (l ! i)))) =
         COLD_START \<or>
         (\<exists>j<Sys_Config.procs conf.
             evnt (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j) = Set_Partition_Mode \<and>
             i_partition (l ! i) = i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j)  \<and>
             (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j) = current (schedule (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j)) \<or>
              part_type (the (partition_conf conf (current (schedule (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j))))) = SYSTEM_PARTITION) \<and>
             part_mode
              (the (part_set_mutex
                     (part_set_restart (part_set_mode p (i_partition (l ! i)) (in_p_mode (l ! i))) (i_partition (l ! i))
                       (in_r_mode (l ! i)))
                     (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0 (i_partition (l ! i)))) =
             in_p_mode (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j))))"
  apply (rule conjI, clarsimp)
  apply (rule conjI)
    apply (drule set_v_guarantee, simp+)
   apply (simp add: part_exists_def part_set_mutex_def part_state_conf_def) 
  apply clarsimp
 apply (rule conjI)
  apply (drule set_v_guarantee', simp+)
  apply (simp add: part_exists_def part_set_mutex_def part_state_conf_def part_set_restart_def part_set_mode_def) 
  by auto

lemma b:"i < Sys_Config.procs conf \<Longrightarrow>
    {s. part_state_conf s} \<inter> \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
    \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>
    \<lbrace>i_partition (\<acute>locals ! i) = p \<and>
     (part_mode (the (p\<rightarrow>\<acute>partitions)) = COLD_START \<or>
      (\<exists>j<Sys_Config.procs conf.
          evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
          p = i_partition (\<acute>locals ! j)  \<and>
          (i_partition (\<acute>locals ! j) = current (schedule (\<acute>locals ! j)) \<or>
           part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) =
           SYSTEM_PARTITION) \<and>
          part_mode (the (p\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j)))\<rbrace> \<inter>
    \<lbrace>\<exists>j<Sys_Config.procs conf.
        evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
        p = i_partition (\<acute>locals ! j) \<and>
        in_p_mode (\<acute>locals ! j) \<noteq> WARM_START \<and>
        (i_partition (\<acute>locals ! j) = current (schedule (\<acute>locals ! j)) \<or>
         part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) =
         SYSTEM_PARTITION)\<rbrace> \<inter>
    - \<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals ! i)) \<and>
       (i_partition (\<acute>locals ! i) = current (schedule (\<acute>locals ! i)) \<or>
        part_type (the (partition_conf conf (current (schedule (\<acute>locals ! i))))) =
        SYSTEM_PARTITION)\<rbrace>
    \<subseteq> {s. s\<lparr>locals_' := locals_' s[i := (locals_' s ! i)\<lparr>ret_n := 0\<rparr>]\<rparr>
           \<in> \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
              \<lbrace>i_partition (\<acute>locals ! i) = p \<and>
               (part_mode (the (p\<rightarrow>\<acute>partitions)) = COLD_START \<or>
                (\<exists>j<Sys_Config.procs conf.
                    evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
                    p = i_partition (\<acute>locals ! j)  \<and>
                    (i_partition (\<acute>locals ! j) = current (schedule (\<acute>locals ! j)) \<or>
                     part_type
                      (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) =
                     SYSTEM_PARTITION) \<and>
                    part_mode (the (p\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j)))\<rbrace>}"
  apply (simp add: part_state_conf_def)
  apply auto 
  by (erule_tac x=ja and P="\<lambda>j. H j \<longrightarrow> K j \<longrightarrow> I j" for H K I in allE, case_tac "i=ja", auto)+ 
  

lemma set_partition_mode_exists_cold_warm':
  "i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> set_partition_mode_system i sat [
            {s. part_state_conf s} \<inter> \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
              \<lbrace>i_partition (\<acute>locals!i) = p\<rbrace> \<inter>
               \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>
              \<lbrace>(part_mode (the (\<acute>partitions  (i_partition (\<acute>locals!i)))) = COLD_START \<or>
                 (\<exists>j<Sys_Config.procs conf.
                  evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
                  i_partition (\<acute>locals ! i) = i_partition (\<acute>locals ! j) \<and>
                 (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
                     part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = 
                       SYSTEM_PARTITION) \<and>
                  part_mode (the (i_partition (\<acute>locals ! i)\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j)))\<rbrace> \<inter>              
              \<lbrace>(\<exists>j<Sys_Config.procs conf.
                evnt (\<acute>locals ! j) = Set_Partition_Mode \<and> 
                i_partition (\<acute>locals ! i) = i_partition (\<acute>locals ! j) \<and>
                in_p_mode (\<acute>locals ! j) \<noteq> WARM_START \<and>
                (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
                    part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = SYSTEM_PARTITION))\<rbrace>,  
            Rely_part i, 
            Guarantee_part  i, 
            \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter> 
      \<lbrace>i_partition (\<acute>locals!i) = p \<and> 
       (part_mode (the (p\<rightarrow>\<acute>partitions)) = COLD_START \<or>
         (\<exists>j<Sys_Config.procs conf.
            evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
            p = i_partition (\<acute>locals ! j) \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = SYSTEM_PARTITION) \<and>
          part_mode (the (p\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j)))\<rbrace>,UNIV]"
  unfolding set_partition_mode_system_def set_partition_mode_def Let_def   
  apply(rule conseqPre[of _ _ _ _ " 
                  {s. part_state_conf s} \<inter> \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
               \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>
              \<lbrace>i_partition (\<acute>locals ! i) = p \<and>
                (part_mode (the (\<acute>partitions  p)) = COLD_START \<or>
                 (\<exists>j<Sys_Config.procs conf.
                  evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
                  p = i_partition (\<acute>locals ! j) \<and>
                 (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
                     part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = 
                       SYSTEM_PARTITION) \<and>
                  part_mode (the (p\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j)))\<rbrace> \<inter>              
              \<lbrace>(\<exists>j<Sys_Config.procs conf.
                evnt (\<acute>locals ! j) = Set_Partition_Mode \<and> 
                p = i_partition (\<acute>locals ! j) \<and>
                in_p_mode (\<acute>locals ! j) \<noteq> WARM_START \<and>
                (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
                    part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = SYSTEM_PARTITION))\<rbrace>"])
  
  apply (rule If, auto simp add: reflexive_Guarantee_Part)
  apply (fastforce intro: Sta_intro pres)+
  apply (rule Seq[of  _ _ _ _ _ _ _ _ "{s. part_state_conf s} \<inter> \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
               \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>
              \<lbrace>i_partition (\<acute>locals ! i) = p \<and>
                (part_mode (the (\<acute>partitions  p)) = COLD_START \<or>
                 (\<exists>j<Sys_Config.procs conf.
                  evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
                  p = i_partition (\<acute>locals ! j) \<and>
                 (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
                     part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = 
                       SYSTEM_PARTITION) \<and>
                  part_mode (the (p\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j)))\<rbrace> \<inter>              
              \<lbrace>(\<exists>j<Sys_Config.procs conf.
                evnt (\<acute>locals ! j) = Set_Partition_Mode \<and> 
                p = i_partition (\<acute>locals ! j) \<and> 
                in_p_mode (\<acute>locals ! j) \<noteq> WARM_START \<and>
                (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
                    part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = SYSTEM_PARTITION))\<rbrace> \<inter>
              \<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals ! i)) \<and>
                                     (i_partition (\<acute>locals ! i) = current (schedule (\<acute>locals ! i)) \<or>
                                      part_type
                                       (the (partition_conf conf (current (schedule (\<acute>locals ! i))))) =
                                      SYSTEM_PARTITION)\<rbrace> \<inter>
                           \<lbrace>part_get_mutex \<acute>partitions (i_partition (\<acute>locals ! i)) = Suc i\<rbrace>"] , 
           auto simp add: reflexive_Guarantee_Part)
  apply (fastforce intro: Sta_intro pres)+  
    apply (rule Await) apply (fastforce intro: Sta_intro pres)+
    apply vcg apply (simp add: exec)
   apply (rule Await) 
      apply (fastforce intro: Sta_intro pres)+ apply auto
   apply vcg  apply (drule exec1, auto)
  apply (rule Basic)
     apply (fastforce intro: Sta_intro pres)+    
   apply (auto simp add: Guarantee_part_def Guarantee_part_set_mode_def part_state_conf_def)[1]  
  using b by auto

lemma set_partition_mode_exists_cold_warm_p:
  "i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> set_partition_mode_system i sat [
            {s. part_state_conf s} \<inter> \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
               \<lbrace>(i_partition (\<acute>locals!i)) = p\<rbrace> \<inter>
               \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>
               \<lbrace>part_mode (the (\<acute>partitions  (i_partition (\<acute>locals!i)))) = COLD_START\<rbrace> \<inter>              
              \<lbrace>(\<exists>j<Sys_Config.procs conf.
                evnt (\<acute>locals ! j) = Set_Partition_Mode \<and> 
                i_partition (\<acute>locals ! i) = i_partition (\<acute>locals ! j) \<and>
                in_p_mode (\<acute>locals ! j) \<noteq> WARM_START \<and>
                (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
                    part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = SYSTEM_PARTITION))\<rbrace>,  
            Rely_part i, 
            Guarantee_part  i, 
            \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter> 
             \<lbrace>(i_partition (\<acute>locals!i)) = p\<rbrace> \<inter>
      \<lbrace>(part_mode (the (i_partition (\<acute>locals ! i)\<rightarrow>\<acute>partitions)) = COLD_START \<or>
         (\<exists>j<Sys_Config.procs conf.
            evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
            i_partition (\<acute>locals ! i) = i_partition (\<acute>locals ! j) \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = SYSTEM_PARTITION) \<and>
          part_mode (the (i_partition (\<acute>locals ! i)\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j)))\<rbrace>,UNIV]"
  apply (rule conseqPrePost[OF 
              inter_pre_post1[OF set_partition_mode_exists_cold_warm' set_partition_mode_eq_i_partition], of _ _ p p])
  by auto                                                                          

lemma exec_ivalid:"i < Sys_Config.procs conf \<Longrightarrow>
       part_state_conf \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr> \<Longrightarrow>
       evnt (l ! i) = Set_Partition_Mode \<Longrightarrow>
       part_mode (the (p (i_partition (l ! i)))) = COLD_START \<or>
       (\<exists>j<Sys_Config.procs conf.
           evnt (l ! j) = Set_Partition_Mode \<and>
           i_partition (l ! i) = i_partition (l ! j) \<and>
           (i_partition (l ! j) = current (schedule (l ! j)) \<or>
            part_type (the (partition_conf conf (current (schedule (l ! j))))) = SYSTEM_PARTITION) \<and>
           part_mode (the (p (i_partition (l ! i)))) = in_p_mode (l ! j)) \<Longrightarrow>       
          in_p_mode (l! i) \<noteq> WARM_START \<Longrightarrow>          
       part_exists p (i_partition (l ! i)) \<Longrightarrow>
       i_partition (l ! i) = current (schedule (l ! i)) \<or>
       part_type (the (partition_conf conf (current (schedule (l ! i))))) = SYSTEM_PARTITION \<Longrightarrow>
       part_get_mutex p (i_partition (l ! i)) = 0 \<Longrightarrow>
       (Normal \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr>,
        Normal
         \<lparr>locals_' = l, timer_' = t,
            partitions_' = part_set_mutex p (i_partition (l ! i)) (Suc i)\<rparr>)
       \<in> Guarantee_part i \<and>
       part_state_conf
        \<lparr>locals_' = l, timer_' = t,
           partitions_' = part_set_mutex p (i_partition (l ! i)) (Suc i)\<rparr> \<and>
       part_exists (part_set_mutex p (i_partition (l ! i)) (Suc i)) (i_partition (l ! i)) \<and>
       (part_mode
         (the (part_set_mutex p (i_partition (l ! i)) (Suc i) (i_partition (l ! i)))) =
        COLD_START \<or>
        (\<exists>j<Sys_Config.procs conf.
            evnt (l ! j) = Set_Partition_Mode \<and>
            i_partition (l ! i) = i_partition (l ! j) \<and>
            (i_partition (l ! j) = current (schedule (l ! j)) \<or>
             part_type (the (partition_conf conf (current (schedule (l ! j))))) = SYSTEM_PARTITION) \<and>
            part_mode
             (the (part_set_mutex p (i_partition (l ! i)) (Suc i) (i_partition (l ! i)))) =
            in_p_mode (l ! j))) \<and>
       part_exists (part_set_mutex p (i_partition (l ! i)) (Suc i)) (i_partition (l ! i)) \<and>
       part_get_mutex (part_set_mutex p (i_partition (l ! i)) (Suc i))
        (i_partition (l ! i)) =
       Suc i" using set_mutex_guarantee set_mutex_part_state_conf 
  apply auto
  unfolding part_exists_def part_set_mutex_def part_get_mutex_def apply auto 
  by (metis option.sel)+
  
lemma set_v_guarantee_i_valid:"i < Sys_Config.procs conf \<Longrightarrow>
    part_state_conf \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr> \<Longrightarrow>
    evnt (l ! i) = Set_Partition_Mode \<Longrightarrow>    
    in_p_mode (l ! i) \<noteq> WARM_START \<Longrightarrow>
    part_exists p (i_partition (l ! i)) \<Longrightarrow>
    i_partition (l ! i) = current (schedule (l ! i)) \<or>
    part_type (the (partition_conf conf (current (schedule (l ! i))))) = SYSTEM_PARTITION \<Longrightarrow>
    part_get_mutex p (i_partition (l ! i)) = Suc i \<Longrightarrow>
    (Normal \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr>,
     Normal
      \<lparr>locals_' = l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>], timer_' = t,
         partitions_' =
           part_set_mutex
            (part_set_restart (part_set_mode p (i_partition (l ! i)) (in_p_mode (l ! i))) (i_partition (l ! i))
              (in_r_mode (l ! i)))
            (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0\<rparr>)
    \<in> Guarantee_part i"
unfolding Guarantee_part_def Guarantee_part_set_mode_def part_set_mutex_def part_get_mutex_def
 part_exists_def current_def part_state_conf_def part_set_restart_def part_set_mode_def
  by auto

lemma exec1_ivalid:" i < Sys_Config.procs conf \<Longrightarrow>
       part_state_conf \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr> \<Longrightarrow>
       evnt (l ! i) = Set_Partition_Mode \<Longrightarrow>
       part_mode (the (p (i_partition (l ! i)))) = COLD_START \<or>
       (\<exists>j<Sys_Config.procs conf.
           evnt (l ! j) = Set_Partition_Mode \<and>
           i_partition (l ! i) = i_partition (l ! j) \<and>
           (i_partition (l ! j) = current (schedule (l ! j)) \<or>
            part_type (the (partition_conf conf (current (schedule (l ! j))))) = SYSTEM_PARTITION) \<and>
           part_mode (the (p (i_partition (l ! i)))) = in_p_mode (l ! j)) \<Longrightarrow>
       in_p_mode (l ! i) \<noteq> WARM_START \<Longrightarrow>
       part_exists p (i_partition (l ! i)) \<Longrightarrow>
       i_partition (l ! i) = current (schedule (l ! i)) \<or>
       part_type (the (partition_conf conf (current (schedule (l ! i))))) = SYSTEM_PARTITION \<Longrightarrow>
       part_get_mutex p (i_partition (l ! i)) = Suc i \<Longrightarrow>
       (Normal \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr>,
        Normal
         \<lparr>locals_' = l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>], timer_' = t,
            partitions_' =
              part_set_mutex
               (part_set_restart (part_set_mode p (i_partition (l ! i)) (in_p_mode (l ! i)))
                 (i_partition (l ! i)) (in_r_mode (l ! i)))
               (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0\<rparr>)
       \<in> Guarantee_part i \<and>
       part_exists
        (part_set_mutex
          (part_set_restart (part_set_mode p (i_partition (l ! i)) (in_p_mode (l ! i)))
            (i_partition (l ! i)) (in_r_mode (l ! i)))
          (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0)
        (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) \<and>
       (\<exists>j<Sys_Config.procs conf.
           evnt (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j) = Set_Partition_Mode \<and>
           i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i) =
           i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j) \<and>
           (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j) =
            current (schedule (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j)) \<or>
            part_type
             (the (partition_conf conf (current (schedule (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j))))) =
            SYSTEM_PARTITION) \<and>
           part_mode
            (the (part_set_mutex
                   (part_set_restart (part_set_mode p (i_partition (l ! i)) (in_p_mode (l ! i)))
                     (i_partition (l ! i)) (in_r_mode (l ! i)))
                   (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0
                   (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)))) =
           in_p_mode (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j))"
  apply (rule conjI)
   apply (drule set_v_guarantee_i_valid,simp+)
  apply (simp add: part_exists_def part_set_mutex_def part_state_conf_def part_set_restart_def part_set_mode_def) 
  by auto

lemma Sta_cond1_ivalid[pres]:"    
    LocalRG_HoareDef.Sta
\<lbrace>(\<exists>j<Sys_Config.procs conf.
          evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
          i_partition (\<acute>locals ! i) = i_partition (\<acute>locals ! j) \<and>
          (i_partition (\<acute>locals ! j) = current (schedule (\<acute>locals ! j)) \<or>
           part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION) \<and>
          part_mode (the (i_partition (\<acute>locals ! i)\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j))\<rbrace>
     (Rely_part i)" 
  apply (simp add: Sta_def) apply clarsimp apply (erule disjE)  
  apply (simp add: Rely_part_def )  
   apply (erule disjE)
    apply (erule exE)  
    apply (simp add: Rely_part_set_mode_def)   
    apply (case_tac "in_p_mode (locals_' x' ! j) \<noteq> 
          part_mode (the (partitions_' y1 (current (schedule (locals_' x' ! j)))))")     
  apply (metis Evnt.distinct(71))
    apply (metis Evnt.distinct(71))
  apply (metis )
   apply (simp add: Rely_part_def)  
  apply (erule disjE)
   apply (erule exE)
   apply (auto simp add: Rely_part_set_mode_def)[1] 
  by fastforce


lemma set_partition_mode_i_exists_cold_warm':
  "i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> set_partition_mode_system i sat [
            {s. part_state_conf s} \<inter>              
             \<lbrace>i_partition (\<acute>locals ! i) = p \<and> 
              (part_mode (the (\<acute>partitions  p)) = COLD_START  \<or>
                 (\<exists>j<Sys_Config.procs conf.
                  evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
                  p = i_partition (\<acute>locals ! j) \<and>
                 (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
                     part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = 
                       SYSTEM_PARTITION) \<and>
                  part_mode (the (p\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j)))\<rbrace> \<inter>
             \<lbrace>  evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>
             \<lbrace>   in_p_mode (\<acute>locals ! i) \<noteq> WARM_START\<rbrace> \<inter>             
             \<lbrace>   part_exists \<acute>partitions (i_partition (\<acute>locals!i)) \<and> 
                 (i_partition (\<acute>locals!i) = (current (schedule (\<acute>locals!i))) \<or> 
                    part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!i)) = SYSTEM_PARTITION)\<rbrace>,  
            Rely_part i, 
            Guarantee_part  i, 
            \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>  \<lbrace>i_partition (\<acute>locals!i) = p\<rbrace> \<inter>
         \<lbrace>(\<exists>j<Sys_Config.procs conf.
            evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
            i_partition (\<acute>locals ! i) = i_partition (\<acute>locals ! j) \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = SYSTEM_PARTITION) \<and>
          part_mode (the (i_partition (\<acute>locals ! i)\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j))\<rbrace>,UNIV]"
  unfolding set_partition_mode_system_def set_partition_mode_def Let_def  
   apply(rule If,auto simp add: reflexive_Guarantee_Part)
apply (fastforce  intro: Sta_intro pres)+  
  apply (rule Seq[of  _ _ _ _ _ _ _ _ "Collect part_state_conf \<inter>
                                    \<lbrace>i_partition (\<acute>locals ! i) = p \<and>
                                     (part_mode (the (p\<rightarrow>\<acute>partitions)) = COLD_START \<or>
                                      (\<exists>j<Sys_Config.procs conf.
                                          evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
                                          p = i_partition (\<acute>locals ! j) \<and>
                                          (i_partition (\<acute>locals ! j) = current (schedule (\<acute>locals ! j)) \<or>
                                           part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) =
                                           SYSTEM_PARTITION) \<and>
                                          part_mode (the (p\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j)))\<rbrace> \<inter>
                                    \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>
                                    \<lbrace>in_p_mode (\<acute>locals ! i) \<noteq> WARM_START\<rbrace> \<inter>
                                    \<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals ! i)) \<and>
                                     (i_partition (\<acute>locals ! i) = current (schedule (\<acute>locals ! i)) \<or>
                                      part_type (the (partition_conf conf (current (schedule (\<acute>locals ! i))))) =
                                      SYSTEM_PARTITION)\<rbrace> \<inter> 
                           \<lbrace>part_get_mutex \<acute>partitions (i_partition (\<acute>locals ! i)) = (Suc i)\<rbrace>"] , 
           auto simp add: reflexive_Guarantee_Part)
  apply (fastforce  intro: Sta_intro pres)+                              
    apply (rule Await)   
       apply (fastforce  intro: Sta_intro pres)+
    apply vcg apply (simp add: exec_ivalid)
apply (rule Await) apply (fastforce  intro: Sta_intro pres)+ apply auto
   apply vcg apply simp apply (frule exec1_ivalid, assumption+) using exec1 apply blast
  apply (rule Basic) 
  by (fastforce  intro: Sta_intro pres)+    


lemma set_partition_mode_i_exists_cold_warm:
  "i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> set_partition_mode_system i sat [
            {s. part_state_conf s} \<inter>              
             \<lbrace>i_partition (\<acute>locals ! i) = p \<and> 
              (part_mode (the (\<acute>partitions  p)) = COLD_START  \<or>
                 (\<exists>j<Sys_Config.procs conf.
                  evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
                  p = i_partition (\<acute>locals ! j) \<and>
                 (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
                     part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = 
                       SYSTEM_PARTITION) \<and>
                  part_mode (the (p\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j)))\<rbrace> \<inter>
             \<lbrace>  evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>
             \<lbrace>   in_p_mode (\<acute>locals ! i) \<noteq> WARM_START\<rbrace> \<inter>             
             \<lbrace>   part_exists \<acute>partitions (i_partition (\<acute>locals!i)) \<and> 
                 (i_partition (\<acute>locals!i) = (current (schedule (\<acute>locals!i))) \<or> 
                    part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!i)) = SYSTEM_PARTITION)\<rbrace>,  
            Rely_part i, 
            Guarantee_part  i, 
            \<lbrace>(i_partition (\<acute>locals!i)) = p\<rbrace> \<inter>
            \<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals ! i))\<rbrace> \<inter>       
            \<lbrace>in_p_mode (\<acute>locals ! i) \<noteq> WARM_START\<rbrace> \<inter> \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace>\<inter>
            \<lbrace>   (i_partition (\<acute>locals!i) = (current (schedule (\<acute>locals!i))) \<or> 
                    part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!i)) = SYSTEM_PARTITION)\<rbrace> \<inter>
         \<lbrace>(\<exists>j<Sys_Config.procs conf.
            evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
            i_partition (\<acute>locals ! i) = i_partition (\<acute>locals ! j) \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = SYSTEM_PARTITION) \<and>
          part_mode (the (i_partition (\<acute>locals ! i)\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j))\<rbrace>,UNIV]"
  apply (rule inter_pre_post[OF set_partition_mode_i_exists_cold_warm'[where p=p] set_partition_mode_locals1[where p=p]])
  by auto

lemma Pre_sta[pres]:"i < Sys_Config.procs conf \<Longrightarrow>
    LocalRG_HoareDef.Sta
     \<lbrace>\<not> part_exists \<acute>partitions (i_partition (\<acute>locals ! i)) \<and> 
       i_partition (\<acute>locals ! i)\<rightarrow>\<acute>partitions = p\<rbrace>
     (Rely_part i)"
  unfolding part_exists_def Rely_part_def Rely_part_set_mode_def Sta_def
  apply clarify
  by auto


lemma set_partition_mode_i_not_part_exists:
  "i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> set_partition_mode_system i sat [{s. part_state_conf s} \<inter>
            \<lbrace> evnt (\<acute>locals ! i) = Set_Partition_Mode \<rbrace> \<inter> 
             \<lbrace> \<not>part_exists \<acute>partitions (i_partition (\<acute>locals!i)) \<and>
              \<acute>partitions (i_partition (\<acute>locals!i)) = p\<rbrace>,  
            Rely_part i, 
            Guarantee_part  i, 
             \<lbrace>\<not>part_exists \<acute>partitions (i_partition (\<acute>locals!i)) \<and> 
              \<acute>partitions (i_partition (\<acute>locals!i)) = p\<rbrace>,UNIV]"
  unfolding set_partition_mode_system_def set_partition_mode_def Let_def  
  apply (rule If, auto simp add: reflexive_Guarantee_Part)
  apply (fastforce intro: Sta_intro pres)+  
  using disjoint_iff_not_equal lrghoare.Conseq apply fastforce
  apply (rule Basic)
     apply (fastforce intro: Sta_intro pres)+  
  unfolding Guarantee_part_def Guarantee_part_set_mode_def part_state_conf_def
  by auto
   


lemma p1[pres]:" LocalRG_HoareDef.Sta
     \<lbrace>
      (\<forall>j<Sys_Config.procs conf.
          i_partition (\<acute>locals ! i) = i_partition (\<acute>locals ! j) \<and>
          evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
          i_partition (\<acute>locals ! j) \<noteq> current (schedule (\<acute>locals ! j)) \<and>
          part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) \<noteq> SYSTEM_PARTITION \<and>
          \<not> part_exists \<acute>partitions (i_partition (\<acute>locals ! j))) \<and>
      i_partition (\<acute>locals ! i)\<rightarrow>\<acute>partitions = p\<rbrace>
     (Rely_part i)"
   apply (simp add: Sta_def) apply clarsimp 
  apply (simp add: Rely_part_def)  
   apply (erule disjE)
    apply (erule exE)  
   apply (simp add: Rely_part_set_mode_def) 
 apply (metis Evnt.distinct(71))
  by auto


lemma b1: "i < procs conf \<Longrightarrow>
           \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>
        \<lbrace>(\<forall>j<Sys_Config.procs conf.
             i_partition (\<acute>locals ! i) = i_partition (\<acute>locals ! j) \<and>
             evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
             i_partition (\<acute>locals ! j) \<noteq> current (schedule (\<acute>locals ! j)) \<and>
             part_type
              (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) \<noteq>
             SYSTEM_PARTITION \<and>
             \<not> part_exists \<acute>partitions (i_partition (\<acute>locals ! j))) \<and>
         i_partition (\<acute>locals ! i)\<rightarrow>\<acute>partitions = p\<rbrace> \<inter>
        \<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals ! i)) \<and>
         (i_partition (\<acute>locals ! i) = current (schedule (\<acute>locals ! i)) \<or>
          part_type
           (the (partition_conf conf (current (schedule (\<acute>locals ! i))))) =
          SYSTEM_PARTITION)\<rbrace> = {}"
  by auto

lemma False_sat:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> C sat [{}, R, G, q,a]"
  by (metis Collect_mem_eq empty_Collect_eq lrghoare.Conseq)

(*lemma Basic_post[pres]:
"LocalRG_HoareDef.Sta
     \<lbrace>(\<forall>j. i_partition (\<acute>locals ! i) = i_partition (\<acute>locals ! j) \<longrightarrow>
           evnt (\<acute>locals ! j) = Set_Partition_Mode \<longrightarrow>
           j < Sys_Config.procs conf \<longrightarrow>
           i_partition (\<acute>locals ! j) \<noteq> current (schedule (\<acute>locals ! j)) \<and>
           part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) \<noteq> SYSTEM_PARTITION) \<and>
      part_mode (the (i_partition (\<acute>locals ! i)\<rightarrow>\<acute>partitions)) = m \<and>
      part_restart (the (i_partition (\<acute>locals ! i)\<rightarrow>\<acute>partitions)) = r\<rbrace>
     (Rely_part i)"
apply (simp add: Sta_def) apply clarsimp 
  apply (simp add: Rely_part_def)  
   apply (erule disjE)
    apply (erule exE)  
   apply (simp add: Rely_part_set_mode_def) 
  apply (metis Evnt.distinct(71))
  by auto *)


lemma modify_ret_eq_vars:" t=s\<lparr>locals_' := locals_' s[i := (locals_' s ! i)\<lparr>ret_n := 0\<rparr>]\<rparr> \<Longrightarrow>
       partitions_' s = partitions_' t \<and>
       (\<forall>j. i_partition (locals_' s!j) = i_partition (locals_' t!j) \<and> 
             evnt (locals_' s!j) = evnt (locals_' t!j) \<and> 
            schedule (locals_' s!j) = schedule (locals_' t!j))"  
  apply (cases "i<length (locals_' s)")    
  apply auto
  by  (case_tac "j\<noteq>i", auto)+
  

lemma modify_ret_guarantee:"
    evnt (locals_' s ! i) = Set_Partition_Mode \<Longrightarrow>
      t = s\<lparr>locals_' := locals_' s[i := (locals_' s ! i)\<lparr>ret_n := 0\<rparr>]\<rparr> \<Longrightarrow>
      (Normal s, Normal t) \<in> Guarantee_part i"
  unfolding Guarantee_part_def Guarantee_part_set_mode_def
  using modify_ret_eq_vars 
  apply (cases "i< length (locals_' s)")
  by auto

lemma Sta_cond1'_not_cold_start[pres]:"    
    LocalRG_HoareDef.Sta
     \<lbrace>(part_mode (the (i_partition (\<acute>locals ! i)\<rightarrow>\<acute>partitions)) = COLD_START \<longrightarrow>
        (\<exists>j<Sys_Config.procs conf.
            evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
            i_partition (\<acute>locals ! i) = i_partition (\<acute>locals ! j) \<and>
            (i_partition (\<acute>locals ! j) = current (schedule (\<acute>locals ! j)) \<or>
             part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION) \<and>
            COLD_START = in_p_mode (\<acute>locals ! j)))\<rbrace>
     (Rely_part i)" 
  apply (simp add: Sta_def) apply clarsimp 
  apply auto
  apply (simp add: Rely_part_def)
     apply (erule disjE)
     apply (erule exE)
     apply (auto simp add: Rely_part_set_mode_def)[1]
    apply fastforce 
  apply (simp add: Rely_part_def)
     apply (erule disjE)
    apply (erule exE)
    apply (simp add: Rely_part_set_mode_def)  
     apply (auto simp add: Rely_part_set_mode_def)[1]
   apply fastforce 
apply (simp add: Rely_part_def)
     apply (erule disjE)
    apply (erule exE)
apply (simp add: Rely_part_set_mode_def)  
     apply (auto simp add: Rely_part_set_mode_def)[1]
  by fastforce 

lemma set_mutex_ivalid_not_cold:
  "i < Sys_Config.procs conf \<Longrightarrow>
     part_state_conf \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr> \<Longrightarrow>
     part_mode (the (p (i_partition (l ! i)))) = COLD_START \<longrightarrow>
     (\<exists>j<Sys_Config.procs conf.
         evnt (l ! j) = Set_Partition_Mode \<and>
         i_partition (l ! i) = i_partition (l ! j) \<and>
         (i_partition (l ! j) = current (schedule (l ! j)) \<or>
          part_type (the (partition_conf conf (current (schedule (l ! j))))) = SYSTEM_PARTITION) \<and>
         COLD_START = in_p_mode (l ! j)) \<Longrightarrow>
     evnt (l ! i) = Set_Partition_Mode \<Longrightarrow>
     part_exists p (i_partition (l ! i)) \<Longrightarrow>
     i_partition (l ! i) = current (schedule (l ! i)) \<or>
     part_type (the (partition_conf conf (current (schedule (l ! i))))) = SYSTEM_PARTITION \<Longrightarrow>
     part_get_mutex p (i_partition (l ! i)) = 0 \<Longrightarrow>
     (Normal \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr>,
      Normal \<lparr>locals_' = l, timer_' = t, partitions_' = part_set_mutex p (i_partition (l ! i)) (Suc i)\<rparr>)
     \<in> Guarantee_part i \<and>
     part_state_conf \<lparr>locals_' = l, timer_' = t, partitions_' = part_set_mutex p (i_partition (l ! i)) (Suc i)\<rparr> \<and>
     (part_mode (the (part_set_mutex p (i_partition (l ! i)) (Suc i) (i_partition (l ! i)))) = COLD_START \<longrightarrow>
      (\<exists>j<Sys_Config.procs conf.
          evnt (l ! j) = Set_Partition_Mode \<and>
          i_partition (l ! i) = i_partition (l ! j) \<and>
          (i_partition (l ! j) = current (schedule (l ! j)) \<or>
           part_type (the (partition_conf conf (current (schedule (l ! j))))) = SYSTEM_PARTITION) \<and>
          COLD_START = in_p_mode (l ! j))) \<and>
     part_exists (part_set_mutex p (i_partition (l ! i)) (Suc i)) (i_partition (l ! i)) \<and>
     part_get_mutex (part_set_mutex p (i_partition (l ! i)) (Suc i)) (i_partition (l ! i)) = Suc i" 
  using set_mutex_guarantee set_mutex_part_state_conf 
  apply auto
  unfolding part_exists_def part_set_mutex_def part_get_mutex_def by auto 

lemma set_v_guarantee_i_valid_not_cold:"i < Sys_Config.procs conf \<Longrightarrow>
    part_state_conf \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr> \<Longrightarrow>
    part_mode (the (p (i_partition (l ! i)))) = COLD_START \<longrightarrow>
    (\<exists>j<Sys_Config.procs conf.
        evnt (l ! j) = Set_Partition_Mode \<and>
        i_partition (l ! i) = i_partition (l ! j) \<and>
        (i_partition (l ! j) = current (schedule (l ! j)) \<or>
         part_type (the (partition_conf conf (current (schedule (l ! j))))) = SYSTEM_PARTITION) \<and>
        COLD_START = in_p_mode (l ! j)) \<Longrightarrow>
    evnt (l ! i) = Set_Partition_Mode \<Longrightarrow>
    part_exists p (i_partition (l ! i)) \<Longrightarrow>
    i_partition (l ! i) = current (schedule (l ! i)) \<or> part_type (the (partition_conf conf (current (schedule (l ! i))))) = SYSTEM_PARTITION \<Longrightarrow>
    part_get_mutex p (i_partition (l ! i)) = Suc i \<Longrightarrow>
    part_mode (the (p (i_partition (l ! i)))) = COLD_START \<longrightarrow> in_p_mode (l ! i) \<noteq> WARM_START \<Longrightarrow>
    (Normal \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr>,
     Normal \<lparr>locals_' = l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>], timer_' = t,
               partitions_' =
                 part_set_mutex
                  (part_set_restart (part_set_mode p (i_partition (l ! i)) (in_p_mode (l ! i))) (i_partition (l ! i)) (in_r_mode (l ! i)))
                  (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0\<rparr>)
    \<in> Guarantee_part i"
unfolding Guarantee_part_def Guarantee_part_set_mode_def part_set_mutex_def part_get_mutex_def
 part_exists_def current_def part_state_conf_def part_set_restart_def part_set_mode_def
  by auto
lemma ret_n_satisfy_post_cond_cold_start:"i < Sys_Config.procs conf \<Longrightarrow>
         part_state_conf \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr> \<Longrightarrow>
         evnt (l ! i) = Set_Partition_Mode \<Longrightarrow>
         part_exists p (i_partition (l ! j)) \<Longrightarrow>
         i_partition (l ! j) = current (schedule (l ! i)) \<or>
         part_type (the (partition_conf conf (current (schedule (l ! i))))) = SYSTEM_PARTITION \<Longrightarrow>
         part_get_mutex p (i_partition (l ! j)) = Suc i \<Longrightarrow>
         part_mode (the (p (i_partition (l ! j)))) = COLD_START \<Longrightarrow>
         in_p_mode (l ! i) = WARM_START \<Longrightarrow>
         j < Sys_Config.procs conf \<Longrightarrow>
         evnt (l ! j) = Set_Partition_Mode \<Longrightarrow>
         i_partition (l ! i) = i_partition (l ! j) \<Longrightarrow>
         i_partition (l ! j) = current (schedule (l ! j)) \<or>
         part_type (the (partition_conf conf (current (schedule (l ! j))))) = SYSTEM_PARTITION \<Longrightarrow>
         COLD_START = in_p_mode (l ! j) \<Longrightarrow>
         part_exists (part_set_mutex p (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i)) 0) (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i)) \<and>
         (\<exists>j<Sys_Config.procs conf.
             evnt (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j) = Set_Partition_Mode \<and>
             i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i) = i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j) \<and>
             (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j) = current (schedule (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j)) \<or>
              part_type (the (partition_conf conf (current (schedule (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j))))) = SYSTEM_PARTITION) \<and>
             part_mode
              (the (part_set_mutex p (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i)) 0 (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i)))) =
             in_p_mode (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j))"
  apply (auto simp add: part_exists_def part_set_mutex_def part_state_conf_def part_set_restart_def part_set_mode_def)
  by (metis (no_types, lifting) nth_list_update_neq partition_mode_type.simps(8)) +

lemma atomic_body_ivalid_not_cold:" i < Sys_Config.procs conf \<Longrightarrow>
       part_state_conf \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr> \<Longrightarrow>
       part_mode (the (p (i_partition (l ! i)))) = COLD_START \<longrightarrow>
       (\<exists>j<Sys_Config.procs conf.
           evnt (l ! j) = Set_Partition_Mode \<and>
           i_partition (l ! i) = i_partition (l ! j) \<and>
           (i_partition (l ! j) = current (schedule (l ! j)) \<or>
            part_type (the (partition_conf conf (current (schedule (l ! j))))) = SYSTEM_PARTITION) \<and>
           COLD_START = in_p_mode (l ! j)) \<Longrightarrow>
       evnt (l ! i) = Set_Partition_Mode \<Longrightarrow>
       part_exists p (i_partition (l ! i)) \<Longrightarrow>
       i_partition (l ! i) = current (schedule (l ! i)) \<or>
       part_type (the (partition_conf conf (current (schedule (l ! i))))) = SYSTEM_PARTITION \<Longrightarrow>
       part_get_mutex p (i_partition (l ! i)) = Suc i \<Longrightarrow>
       (part_mode (the (p (i_partition (l ! i)))) = COLD_START \<and> in_p_mode (l ! i) = WARM_START \<longrightarrow>
        (Normal \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr>,
         Normal \<lparr>locals_' = l[i := (l ! i)\<lparr>ret_n := 0\<rparr>], timer_' = t,
                   partitions_' = part_set_mutex p (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i)) 0\<rparr>)
        \<in> Guarantee_part i \<and>
        part_exists (part_set_mutex p (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i)) 0)
         (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i)) \<and>
        (\<exists>j<Sys_Config.procs conf.
            evnt (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j) = Set_Partition_Mode \<and>
            i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i) = i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j) \<and>
            (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j) = current (schedule (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j)) \<or>
             part_type (the (partition_conf conf (current (schedule (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j))))) = SYSTEM_PARTITION) \<and>
            part_mode
             (the (part_set_mutex p (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i)) 0
                    (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i)))) =
            in_p_mode (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j))) \<and>
       ((part_mode (the (p (i_partition (l ! i)))) = COLD_START \<longrightarrow> in_p_mode (l ! i) \<noteq> WARM_START) \<longrightarrow>
        (Normal \<lparr>locals_' = l, timer_' = t, partitions_' = p\<rparr>,
         Normal \<lparr>locals_' = l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>], timer_' = t,
                   partitions_' =
                     part_set_mutex
                      (part_set_restart (part_set_mode p (i_partition (l ! i)) (in_p_mode (l ! i))) (i_partition (l ! i))
                        (in_r_mode (l ! i)))
                      (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0\<rparr>)
        \<in> Guarantee_part i \<and>
        part_exists
         (part_set_mutex
           (part_set_restart (part_set_mode p (i_partition (l ! i)) (in_p_mode (l ! i))) (i_partition (l ! i))
             (in_r_mode (l ! i)))
           (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0)
         (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) \<and>
        (\<exists>j<Sys_Config.procs conf.
            evnt (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j) = Set_Partition_Mode \<and>
            i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i) = i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j) \<and>
            (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j) = current (schedule (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j)) \<or>
             part_type (the (partition_conf conf (current (schedule (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j))))) = SYSTEM_PARTITION) \<and>
            part_mode
             (the (part_set_mutex
                    (part_set_restart (part_set_mode p (i_partition (l ! i)) (in_p_mode (l ! i))) (i_partition (l ! i))
                      (in_r_mode (l ! i)))
                    (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0
                    (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)))) =
            in_p_mode (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j)))"  
  apply (rule conjI)+
   apply clarify
  apply (rule conjI)+
  apply (drule set_v_guarantee,simp+)
   apply (drule ret_n_satisfy_post_cond_cold_start,simp+)
  apply clarify
  apply (rule conjI)+
  apply (drule set_v_guarantee_i_valid_not_cold,simp+)
  by (auto simp add: part_exists_def part_set_mutex_def part_state_conf_def part_set_restart_def part_set_mode_def) 


lemma [pres]:"Sta \<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals!i))\<rbrace> (Rely_part i)"
   unfolding Sta_def  Rely_part_def  Rely_part_set_mode_def  
  by fastforce

lemma set_partition_mode_i_not_cold:
  "i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> set_partition_mode_system i sat [
            {s. part_state_conf s} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>
            \<lbrace>part_mode (the (\<acute>partitions  (i_partition (\<acute>locals!i)))) \<noteq> COLD_START  \<or>
                 (\<exists>j<Sys_Config.procs conf.
                  evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
                  i_partition (\<acute>locals ! i) = i_partition (\<acute>locals ! j) \<and>
                 (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
                     part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = 
                       SYSTEM_PARTITION) \<and>
                  part_mode (the (i_partition (\<acute>locals ! i)\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j))\<rbrace> \<inter>
            \<lbrace> part_exists \<acute>partitions (i_partition (\<acute>locals!i)) \<and>  
              (i_partition (\<acute>locals!i) = (current (schedule (\<acute>locals!i))) \<or> 
              part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!i)) = SYSTEM_PARTITION)\<rbrace>,  
            Rely_part i, 
            Guarantee_part  i, 
         \<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals ! i))\<rbrace> \<inter>       
         \<lbrace>(\<exists>j<Sys_Config.procs conf.
            evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
            i_partition (\<acute>locals ! i) = i_partition (\<acute>locals ! j) \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = SYSTEM_PARTITION) \<and>
          part_mode (the (i_partition (\<acute>locals ! i)\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j))\<rbrace>,UNIV]"
unfolding set_partition_mode_system_def set_partition_mode_def Let_def  
  apply (rule If) apply(auto simp add: reflexive_Guarantee_Part )
  apply (fastforce intro: Sta_intro pres)+  
apply (rule Seq[of  _ _ _ _ _ _ _ _ "{s. part_state_conf s} \<inter>
                            \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>
                                    \<lbrace>part_mode (the (i_partition (\<acute>locals ! i)\<rightarrow>\<acute>partitions)) = COLD_START \<longrightarrow>
                                     (\<exists>j<Sys_Config.procs conf.
                                         evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
                                         i_partition (\<acute>locals ! i) = i_partition (\<acute>locals ! j) \<and>
                                         (i_partition (\<acute>locals ! j) = current (schedule (\<acute>locals ! j)) \<or>
                                          part_type
                                           (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) =
                                          SYSTEM_PARTITION) \<and>
                                         COLD_START = in_p_mode (\<acute>locals ! j))\<rbrace> \<inter>
                                    \<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals ! i)) \<and>
                                     (i_partition (\<acute>locals ! i) = current (schedule (\<acute>locals ! i)) \<or>
                                      part_type
                                       (the (partition_conf conf (current (schedule (\<acute>locals ! i))))) =
                                      SYSTEM_PARTITION)\<rbrace> \<inter> 
                           \<lbrace>part_get_mutex \<acute>partitions (i_partition (\<acute>locals ! i)) = (Suc i)\<rbrace>"] , 
           auto simp only: reflexive_Guarantee_Part)
  apply (fastforce intro: Sta_intro pres)+                             
  apply (rule Await) 
apply (fastforce intro: Sta_intro pres)+ 
    apply vcg apply simp  using set_mutex_ivalid_not_cold apply blast  
apply (rule Await) apply (fastforce intro: Sta_intro pres)+
  apply auto
   apply vcg apply (simp add: atomic_body_ivalid_not_cold)
  apply (rule Basic)
  by (fastforce intro: Sta_intro pres)+


lemma set_partition_mode_i_not_cold_p:
  "i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> set_partition_mode_system i sat [
            {s. part_state_conf s} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>            
            \<lbrace>i_partition (\<acute>locals!i) = p \<and> (part_mode (the (\<acute>partitions  p)) \<noteq> COLD_START \<or>
               (\<exists>j<Sys_Config.procs conf.
                  evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
                  p = i_partition (\<acute>locals ! j) \<and>
                 (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
                     part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = 
                       SYSTEM_PARTITION) \<and>
                  part_mode (the (p\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j)))\<rbrace> \<inter>
            \<lbrace>   part_exists \<acute>partitions (i_partition (\<acute>locals!i)) \<and> 
                 (i_partition (\<acute>locals!i) = (current (schedule (\<acute>locals!i))) \<or> 
                    part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!i)) = SYSTEM_PARTITION)\<rbrace>,  
            Rely_part i, 
            Guarantee_part  i, 
         \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>     
         \<lbrace>i_partition (\<acute>locals!i) = p\<rbrace> \<inter> 
         \<lbrace>(p = (current (schedule (\<acute>locals!i))) \<or> 
              part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!i)) = SYSTEM_PARTITION)\<rbrace> \<inter>
         \<lbrace>(\<exists>j<Sys_Config.procs conf.
            evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
            p = i_partition (\<acute>locals ! j) \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = SYSTEM_PARTITION) \<and>
          part_mode (the (p\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j))\<rbrace>,UNIV]"  
  apply (rule inter_pre_post[OF set_partition_mode_i_not_cold 
                                set_partition_mode_locals''[where p=p]])
  by auto
  
  

lemma execute_service:" i < Sys_Config.procs conf \<Longrightarrow>
  Sta P' R \<Longrightarrow> 
  \<forall>s. (Normal s, Normal s) \<in> G \<Longrightarrow>
  \<forall>n. Sta \<lbrace>evnt (\<acute>locals ! i) = n\<rbrace> R \<Longrightarrow>
   \<forall>n. Sta (-\<lbrace>evnt (\<acute>locals ! i) = n\<rbrace>) R \<Longrightarrow>
   Sta \<lbrace>False\<rbrace> R \<Longrightarrow>
   P  \<subseteq> P' \<Longrightarrow> m = Get_Partition_Status \<or> m = Set_Partition_Mode \<Longrightarrow>
   P' \<inter> \<lbrace>evnt (\<acute>locals ! i) \<noteq> m\<rbrace> = {} \<Longrightarrow>
   \<Gamma> (m,i) = Some (f i) \<Longrightarrow>
   \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (f i) sat [P', R, G, Q, A] \<Longrightarrow>      
    \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> execute_service i sat [P , R, G, Q, A]" 
apply (rule conseqPre[of _ _ _ _ "P'"], auto)
  unfolding execute_service_def
  apply (rule If, auto)
   apply (rule Call, auto intro: body )
    apply (rule Sta_intro,auto)                   
    apply (fastforce intro: conseqPre[of _ _ _ _ "P'"])
          apply (fastforce intro: conseqPre[OF False_sat])         
  apply (rule If, auto)  
   apply (rule Call, auto intro: body )
    apply (simp add: LocalRG_HoareDef.Sta_def, fastforce)                           
    apply (fastforce intro: conseqPre[OF False_sat] conseqPre[of _ _ _ _ "P'"])
           apply (rule If, auto)  
    apply (simp add: LocalRG_HoareDef.Sta_def, fastforce)     
   apply (cases m,auto)  apply (rule Call, auto intro: body ) 
    apply (simp add: LocalRG_HoareDef.Sta_def, fastforce)   
 apply (fastforce intro:  conseqPre[of _ _ _ _ "P'"] )   
  by (fastforce intro: conseqPre[OF False_sat])

lemma cold_start_comp4:
  " i < Sys_Config.procs conf \<Longrightarrow>
    \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> execute_service i sat [Collect part_state_conf \<inter> \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
      \<lbrace>part_mode (the (p\<rightarrow>\<acute>partitions)) = COLD_START\<rbrace> \<inter>      
      \<lbrace>(i_partition (\<acute>locals ! i) = p \<and>
        evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
        (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION) \<and>
        in_p_mode (\<acute>locals ! i) \<noteq> WARM_START)\<rbrace>, Rely_part i, Guarantee_part i, 
       \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
       \<lbrace>(\<exists>j<Sys_Config.procs conf.
           i_partition (\<acute>locals ! j) = p \<and>
           evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
           (i_partition (\<acute>locals ! j) = current (schedule (\<acute>locals ! j)) \<or>
            part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION) \<and>
           in_p_mode (\<acute>locals ! j) \<noteq> WARM_START) \<and>
            (i_partition (\<acute>locals ! i) = p \<and>  evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
            (i_partition (\<acute>locals ! i) = current (schedule (\<acute>locals ! i)) \<or>
             part_type (the (partition_conf conf (current (schedule (\<acute>locals ! i))))) = SYSTEM_PARTITION) \<and>
              in_p_mode (\<acute>locals ! i) \<noteq> WARM_START \<longrightarrow> 
            (\<exists>k<Sys_Config.procs conf.
               i_partition (\<acute>locals ! k) = p \<and>   evnt (\<acute>locals ! k) = Set_Partition_Mode \<and>
              (i_partition (\<acute>locals ! k) = current (schedule (\<acute>locals ! k)) \<or>
              part_type (the (partition_conf conf (current (schedule (\<acute>locals ! k))))) = SYSTEM_PARTITION) \<and>
              part_mode (the (i_partition (\<acute>locals ! k)\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! k)))\<rbrace>,UNIV]"
   apply(rule conseqPre[of _ _ _ _ "Collect part_state_conf \<inter> 
      \<lbrace>i_partition (\<acute>locals ! i) = p \<and> (part_mode (the (p\<rightarrow>\<acute>partitions)) = COLD_START \<or>
               (\<exists>j<Sys_Config.procs conf.
                  evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
                  p = i_partition (\<acute>locals ! j) \<and>
                 (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
                     part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = 
                       SYSTEM_PARTITION) \<and>
                  part_mode (the (p\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j)))\<rbrace> \<inter>      
      \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>
        \<lbrace>part_exists \<acute>partitions p \<and> (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION) \<rbrace> \<inter>
        \<lbrace>in_p_mode (\<acute>locals ! i) \<noteq> WARM_START\<rbrace>"], auto)     
  apply (rule conseqPrePost[OF execute_service[OF _ _ _ _ _ _ _ _ _ _ set_partition_mode_i_exists_cold_warm[where p="p"], 
          where  m="Set_Partition_Mode" and P="Collect part_state_conf \<inter> 
      \<lbrace>i_partition (\<acute>locals ! i) = p \<and> (part_mode (the (p\<rightarrow>\<acute>partitions)) = COLD_START \<or>
               (\<exists>j<Sys_Config.procs conf.
                  evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
                  p = i_partition (\<acute>locals ! j) \<and>
                 (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
                     part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = 
                       SYSTEM_PARTITION) \<and>
                  part_mode (the (p\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j)))\<rbrace> \<inter>      
      \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>
        \<lbrace>part_exists \<acute>partitions p \<and> (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION) \<rbrace> \<inter>
        \<lbrace>in_p_mode (\<acute>locals ! i) \<noteq> WARM_START\<rbrace>"]], assumption+, auto)
  apply (fastforce intro: Sta_intro pres)+
               apply (auto simp add: reflexive_Guarantee_Part)[1]
              apply (fastforce intro: Sta_intro pres)+
  by (auto simp add: current_def body)



lemma exec_ivalid_cold1:"i < Sys_Config.procs conf \<Longrightarrow>
       part_state_conf \<lparr>locals_' = l, timer_' = t, partitions_' = part\<rparr> \<Longrightarrow>
       part_exists part p \<Longrightarrow>
       evnt (l ! i) = Set_Partition_Mode \<Longrightarrow>
       i_partition (l ! i) = p \<longrightarrow>
       p \<noteq> schedule (l ! i) \<and>
       part_type (the (partition_conf conf (schedule (l ! i)))) \<noteq> SYSTEM_PARTITION \<or>
       in_p_mode (l ! i) = WARM_START \<Longrightarrow>
       \<exists>j<Sys_Config.procs conf.
          evnt (l ! j) = Set_Partition_Mode \<and>
          p = i_partition (l ! j) \<and>
          in_p_mode (l ! j) \<noteq> WARM_START \<and>
          (i_partition (l ! j) = current (schedule (l ! j)) \<or>
           part_type (the (partition_conf conf (current (schedule (l ! j))))) = SYSTEM_PARTITION) \<Longrightarrow>
       part_exists part (i_partition (l ! i)) \<Longrightarrow>
       i_partition (l ! i) = current (schedule (l ! i)) \<or>
       part_type (the (partition_conf conf (current (schedule (l ! i))))) = SYSTEM_PARTITION \<Longrightarrow>
       part_get_mutex part (i_partition (l ! i)) = 0 \<Longrightarrow>
       (Normal \<lparr>locals_' = l, timer_' = t, partitions_' = part\<rparr>,
        Normal
         \<lparr>locals_' = l, timer_' = t,
            partitions_' = part_set_mutex part (i_partition (l ! i)) (Suc i)\<rparr>)
       \<in> Guarantee_part i \<and>
       part_state_conf
        \<lparr>locals_' = l, timer_' = t,
           partitions_' = part_set_mutex part (i_partition (l ! i)) (Suc i)\<rparr> \<and>
       part_exists (part_set_mutex part (i_partition (l ! i)) (Suc i)) p \<and>
       part_exists (part_set_mutex part (i_partition (l ! i)) (Suc i))
        (i_partition (l ! i)) \<and>
       part_get_mutex (part_set_mutex part (i_partition (l ! i)) (Suc i))
        (i_partition (l ! i)) =
       Suc i"   
  apply (auto intro: set_mutex_guarantee set_mutex_part_state_conf) 
  unfolding part_exists_def part_set_mutex_def part_get_mutex_def  by auto

lemma exec_nop:" i < Sys_Config.procs conf \<Longrightarrow>
       part_state_conf \<lparr>locals_' = l, timer_' = t, partitions_' = part\<rparr> \<Longrightarrow>
       part_exists part p \<Longrightarrow>
       evnt (l ! i) = Set_Partition_Mode \<Longrightarrow>
       i_partition (l ! i) = p \<longrightarrow>
       p \<noteq> schedule (l ! i) \<and>
       part_type (the (partition_conf conf (schedule (l ! i)))) \<noteq> SYSTEM_PARTITION \<or>
       in_p_mode (l ! i) = WARM_START \<Longrightarrow>
       \<exists>j<Sys_Config.procs conf.
          evnt (l ! j) = Set_Partition_Mode \<and>
          p = i_partition (l ! j) \<and>
          in_p_mode (l ! j) \<noteq> WARM_START \<and>
          (i_partition (l ! j) = current (schedule (l ! j)) \<or>
           part_type (the (partition_conf conf (current (schedule (l ! j))))) = SYSTEM_PARTITION) \<Longrightarrow>
       part_exists part (i_partition (l ! i)) \<Longrightarrow>
       i_partition (l ! i) = current (schedule (l ! i)) \<or>
       part_type (the (partition_conf conf (current (schedule (l ! i))))) = SYSTEM_PARTITION \<Longrightarrow>
       part_get_mutex part (i_partition (l ! i)) = Suc i \<Longrightarrow>
       (part_mode (the (part (i_partition (l ! i)))) = COLD_START \<and>
        in_p_mode (l ! i) = WARM_START \<longrightarrow>
        (Normal \<lparr>locals_' = l, timer_' = t, partitions_' = part\<rparr>,
         Normal
          \<lparr>locals_' = l[i := (l ! i)\<lparr>ret_n := 0\<rparr>], timer_' = t,
             partitions_' =
               part_set_mutex part (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i)) 0\<rparr>)
        \<in> Guarantee_part i \<and>
        part_exists (part_set_mutex part (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i)) 0)
         p \<and>
        (\<exists>j<Sys_Config.procs conf.
            evnt (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j) = Set_Partition_Mode \<and>
            p = i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j) \<and>
            in_p_mode (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j) \<noteq> WARM_START \<and>
            (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j) =
             current (schedule (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j)) \<or>
             part_type
              (the (partition_conf conf (current (schedule (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j))))) =
             SYSTEM_PARTITION)) \<and>
        (evnt (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i) = Set_Partition_Mode \<longrightarrow>
         i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i) = p \<longrightarrow>
         p \<noteq> schedule (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i) \<and>
         part_type (the (partition_conf conf (schedule (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i)))) \<noteq>
         SYSTEM_PARTITION \<or>
         in_p_mode (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i) = WARM_START)) \<and>
       ((part_mode (the (part (i_partition (l ! i)))) = COLD_START \<longrightarrow>
         in_p_mode (l ! i) \<noteq> WARM_START) \<longrightarrow>
        (Normal \<lparr>locals_' = l, timer_' = t, partitions_' = part\<rparr>,
         Normal
          \<lparr>locals_' = l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>], timer_' = t,
             partitions_' =
               part_set_mutex
                (part_set_restart
                  (part_set_mode part (i_partition (l ! i)) (in_p_mode (l ! i)))
                  (i_partition (l ! i)) (in_r_mode (l ! i)))
                (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0\<rparr>)
        \<in> Guarantee_part i \<and>
        part_exists
         (part_set_mutex
           (part_set_restart (part_set_mode part (i_partition (l ! i)) (in_p_mode (l ! i)))
             (i_partition (l ! i)) (in_r_mode (l ! i)))
           (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0)
         p \<and>
        (\<exists>j<Sys_Config.procs conf.
            evnt (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j) = Set_Partition_Mode \<and>
            p = i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j) \<and>
            in_p_mode (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j) \<noteq> WARM_START \<and>
            (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j) =
             current (schedule (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j)) \<or>
             part_type
              (the (partition_conf conf
                     (current (schedule (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j))))) =
             SYSTEM_PARTITION)) \<and>
        (evnt (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i) = Set_Partition_Mode \<longrightarrow>
         i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i) = p \<longrightarrow>
         p \<noteq> schedule (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i) \<and>
         part_type (the (partition_conf conf (schedule (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)))) \<noteq>
         SYSTEM_PARTITION \<or>
         in_p_mode (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i) = WARM_START))"
apply (rule conjI)
   apply clarify
   apply (rule conjI)
    apply (drule set_v_guarantee,simp+)
apply (rule conjI)+
  apply (auto simp add:  part_exists_def part_set_mutex_def  part_set_restart_def part_set_mode_def)[1]
   apply (rule conjI)+
    apply (metis (no_types) nth_list_update_neq) 
   apply (auto simp: part_state_conf_def)[1] 
  apply clarify
  apply (rule conjI)
   apply (frule set_v_guarantee',simp+)
  apply (rule conjI)
   apply (auto simp add: part_exists_def part_set_mutex_def  part_set_restart_def part_set_mode_def)[1]
  apply (rule conjI)
  apply (metis (no_types) current_def nth_list_update_neq)
  by (auto simp: part_state_conf_def)[1]

lemma cold_start_comp2':
  " i < Sys_Config.procs conf \<Longrightarrow>
    \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> set_partition_mode_system i 
    sat [Collect part_state_conf \<inter> \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter> \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>         
      \<lbrace>\<not>(i_partition (\<acute>locals ! i) = p \<and>
        evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
        (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION) \<and>
        in_p_mode (\<acute>locals ! i) \<noteq> WARM_START)\<rbrace> \<inter>                       
      \<lbrace>\<exists>j<Sys_Config.procs conf.
           evnt (\<acute>locals ! j) = Set_Partition_Mode \<and> 
          p = i_partition (\<acute>locals ! j) \<and>
           in_p_mode (\<acute>locals ! j) \<noteq> WARM_START \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION)\<rbrace>, 
       Rely_part i, Guarantee_part i, 
       \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
       \<lbrace>\<exists>j<Sys_Config.procs conf.
            evnt (\<acute>locals ! j) = Set_Partition_Mode \<and> 
          p = i_partition (\<acute>locals ! j) \<and>
           in_p_mode (\<acute>locals ! j) \<noteq> WARM_START \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION)\<rbrace> \<inter>
        \<lbrace>\<not>(i_partition (\<acute>locals ! i) = p \<and>
        evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
        (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION) \<and>
        in_p_mode (\<acute>locals ! i) \<noteq> WARM_START)\<rbrace>,UNIV]"
  unfolding set_partition_mode_system_def set_partition_mode_def Let_def  
  apply (rule If)  apply (fastforce intro: Sta_intro pres)+  apply(auto simp add: reflexive_Guarantee_Part )[1]
apply (rule Seq[of  _ _ _ _ _ _ _ _ "Collect part_state_conf \<inter> \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter> \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>       
      \<lbrace>\<not>(i_partition (\<acute>locals ! i) = p \<and>
        evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
        (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION) \<and>
        in_p_mode (\<acute>locals ! i) \<noteq> WARM_START)\<rbrace> \<inter>                       
      \<lbrace>\<exists>j<Sys_Config.procs conf.
           evnt (\<acute>locals ! j) = Set_Partition_Mode \<and> 
          p = i_partition (\<acute>locals ! j) \<and>
           in_p_mode (\<acute>locals ! j) \<noteq> WARM_START \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION)\<rbrace>  \<inter>
      \<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals ! i)) \<and>
       (i_partition (\<acute>locals ! i) = current (schedule (\<acute>locals ! i)) \<or>
        part_type ((the \<circ> partition_conf conf \<circ> current \<circ> schedule) (\<acute>locals ! i)) = SYSTEM_PARTITION)\<rbrace> \<inter>
                           \<lbrace>part_get_mutex \<acute>partitions (i_partition (\<acute>locals ! i)) = (Suc i)\<rbrace>"]) 
apply (fastforce intro: Sta_intro pres)+                             
  apply (auto simp only: reflexive_Guarantee_Part)  
  apply (rule Await) 
apply (fastforce intro: Sta_intro pres)+ 
    apply vcg apply simp  apply (frule exec_ivalid_cold1,blast+)  
apply (rule Await) apply (fastforce intro: Sta_intro pres)+  
   apply vcg apply simp apply (simp add: exec_nop)
  apply (rule Basic)    
     apply (fastforce intro: Sta_intro pres)+
   apply (auto simp add: Guarantee_part_def Guarantee_part_set_mode_def part_state_conf_def)[1]  
  apply clarify
  apply (simp add: part_state_conf_def)
  by (metis (no_types)  nth_list_update_neq)

lemma cold_start_comp2'':
  " i < Sys_Config.procs conf \<Longrightarrow>
    \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> get_partition_status i 
    sat [Collect part_state_conf \<inter> \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>   
      \<lbrace>\<not>(i_partition (\<acute>locals ! i) = p \<and>
        evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
        (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION) \<and>
        in_p_mode (\<acute>locals ! i) \<noteq> WARM_START)\<rbrace> \<inter>                       
      \<lbrace>\<exists>j<Sys_Config.procs conf.
           evnt (\<acute>locals ! j) = Set_Partition_Mode \<and> 
          p = i_partition (\<acute>locals ! j) \<and>
           in_p_mode (\<acute>locals ! j) \<noteq> WARM_START \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION)\<rbrace> \<inter>
      \<lbrace>evnt (\<acute>locals ! i) = Get_Partition_Status\<rbrace>, 
       Rely_part i, Guarantee_part i, 
       \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
       \<lbrace>\<exists>j<Sys_Config.procs conf.
            evnt (\<acute>locals ! j) = Set_Partition_Mode \<and> 
          p = i_partition (\<acute>locals ! j) \<and>
           in_p_mode (\<acute>locals ! j) \<noteq> WARM_START \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION)\<rbrace> \<inter>
        \<lbrace>\<not>(i_partition (\<acute>locals ! i) = p \<and>
        evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
        (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION) \<and>
        in_p_mode (\<acute>locals ! i) \<noteq> WARM_START)\<rbrace>,UNIV]"
  unfolding get_partition_status_def Let_def  
apply (rule Basic)  
     apply (fastforce intro: Sta_intro pres)+
   apply (auto simp add: Guarantee_part_def Guarantee_part_get_state_def part_state_conf_def)[1]  
  apply clarify
  apply (simp add: part_state_conf_def) 
  by (metis (no_types, lifting) Evnt.distinct(67) nth_list_update_neq)


lemma cold_start_comp2:
  " i < Sys_Config.procs conf \<Longrightarrow>
    \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> execute_service i 
    sat [Collect part_state_conf \<inter> \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
      \<lbrace>part_mode (the (p\<rightarrow>\<acute>partitions)) = COLD_START\<rbrace> \<inter>      
      \<lbrace>\<not>(i_partition (\<acute>locals ! i) = p \<and>
        evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
        (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION) \<and>
        in_p_mode (\<acute>locals ! i) \<noteq> WARM_START)\<rbrace> \<inter>                       
      \<lbrace>\<exists>j<Sys_Config.procs conf.
          i_partition (\<acute>locals ! j) = p \<and>
          evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
          in_p_mode (\<acute>locals ! j) \<noteq> WARM_START \<and>
          (i_partition (\<acute>locals ! j) = current (schedule (\<acute>locals ! j)) \<or>
           part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) =
           SYSTEM_PARTITION)\<rbrace>, Rely_part i, Guarantee_part i, 
       \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
       \<lbrace>(\<exists>j<Sys_Config.procs conf.
           i_partition (\<acute>locals ! j) = p \<and>
           evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
           (i_partition (\<acute>locals ! j) = current (schedule (\<acute>locals ! j)) \<or>
            part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION) \<and>
           in_p_mode (\<acute>locals ! j) \<noteq> WARM_START) \<and>
            (i_partition (\<acute>locals ! i) = p \<and>  evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
            (i_partition (\<acute>locals ! i) = current (schedule (\<acute>locals ! i)) \<or>
             part_type (the (partition_conf conf (current (schedule (\<acute>locals ! i))))) = SYSTEM_PARTITION) \<and>
              in_p_mode (\<acute>locals ! i) \<noteq> WARM_START \<longrightarrow> 
            (\<exists>k<Sys_Config.procs conf.
               i_partition (\<acute>locals ! k) = p \<and>   evnt (\<acute>locals ! k) = Set_Partition_Mode \<and>
              (i_partition (\<acute>locals ! k) = current (schedule (\<acute>locals ! k)) \<or>
              part_type (the (partition_conf conf (current (schedule (\<acute>locals ! k))))) = SYSTEM_PARTITION) \<and>
              part_mode (the (i_partition (\<acute>locals ! k)\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! k)))\<rbrace>,UNIV]"
apply (rule conseqPrePost[of _ _ _ _ "Collect part_state_conf \<inter> \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>         
      \<lbrace>\<not>(i_partition (\<acute>locals ! i) = p \<and>
        evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
        (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION) \<and>
        in_p_mode (\<acute>locals ! i) \<noteq> WARM_START)\<rbrace> \<inter>                       
      \<lbrace>\<exists>j<Sys_Config.procs conf.
           evnt (\<acute>locals ! j) = Set_Partition_Mode \<and> 
          p = i_partition (\<acute>locals ! j) \<and>
           in_p_mode (\<acute>locals ! j) \<noteq> WARM_START \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION)\<rbrace>" "Rely_part i" "Guarantee_part i"
     "\<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
       \<lbrace>\<exists>j<Sys_Config.procs conf.
            evnt (\<acute>locals ! j) = Set_Partition_Mode \<and> 
          p = i_partition (\<acute>locals ! j) \<and>
           in_p_mode (\<acute>locals ! j) \<noteq> WARM_START \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION)\<rbrace> \<inter>
        \<lbrace>\<not>(i_partition (\<acute>locals ! i) = p \<and>
        evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
        (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION) \<and>
        in_p_mode (\<acute>locals ! i) \<noteq> WARM_START)\<rbrace>"])  
  unfolding execute_service_def
  apply (rule If)  
      apply (fastforce intro: Sta_intro pres)
     apply(auto simp add: reflexive_Guarantee_Part )[1]
    apply (rule Call)
       apply (fastforce intro: Sta_intro pres)
      apply(auto simp add: reflexive_Guarantee_Part )[1]
         apply ( auto simp add: body)[2]
  apply (blast intro:  conseqPrePost[OF cold_start_comp2''])
    apply (rule If)  
          apply (fastforce intro: Sta_intro pres)
         apply(auto simp add: reflexive_Guarantee_Part )[1]
    apply (rule Call)
       apply (fastforce intro: Sta_intro pres)
      apply(auto simp add: reflexive_Guarantee_Part )[1]
         apply ( auto simp add: body)[2]
        apply (blast intro:  conseqPrePost[OF cold_start_comp2'])
       apply (rule conseqPre) 
        apply (rule Skip)
         apply (fastforce intro: Sta_intro pres)
by (auto simp add: current_def reflexive_Guarantee_Part)
 
lemma Part_mode_cold:
"\<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> 
  (COBEGIN SCHEME [0 \<le> i < procs conf]
  (execute_service i, 
    Collect part_state_conf \<inter> 
      \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
      \<lbrace>part_mode (the (\<acute>partitions  p)) = COLD_START\<rbrace> \<inter>
      \<lbrace>\<exists>j. j< procs conf \<and> 
        (i_partition (\<acute>locals!j)) = p \<and> 
        evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>                             
        in_p_mode (\<acute>locals ! j) \<noteq> WARM_START \<and>
        (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
          part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = SYSTEM_PARTITION)\<rbrace>,  
      Rely_part i, Guarantee_part  i, 
      \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter> 
        \<lbrace>(\<exists>j< procs conf.
          (i_partition (\<acute>locals!j)) = p \<and>                 
          evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
          part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = SYSTEM_PARTITION) \<and>
          in_p_mode (\<acute>locals ! j) \<noteq> WARM_START) \<and>
         (((i_partition (\<acute>locals!i)) = p \<and>                 
          evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
          (i_partition (\<acute>locals!i) = (current (schedule (\<acute>locals!i))) \<or> 
          part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!i)) = SYSTEM_PARTITION) \<and>
          in_p_mode (\<acute>locals ! i) \<noteq> WARM_START ) \<longrightarrow> 
            (\<exists>k< procs conf.
              i_partition (\<acute>locals!k) = p \<and>
              evnt (\<acute>locals ! k) = Set_Partition_Mode \<and>
             (i_partition (\<acute>locals!k) = (current (schedule (\<acute>locals!k))) \<or> 
              part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!k)) = SYSTEM_PARTITION) \<and> 
              part_mode (the (i_partition (\<acute>locals ! k)\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! k))) 
                \<rbrace>,UNIV)
  COEND)
  SAT [{s. part_state_conf s} \<inter> \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
      \<lbrace>part_mode (the (\<acute>partitions  p)) = COLD_START\<rbrace> \<inter>
       \<lbrace>\<exists>j. j<procs conf \<and> 
       (i_partition (\<acute>locals!j)) = p \<and>        
       evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>                             
        in_p_mode (\<acute>locals ! j) \<noteq> WARM_START \<and>
        (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = SYSTEM_PARTITION)\<rbrace>, 
      Id, {(x,y). \<exists>nx ny. x=Normal nx \<and> y=Normal ny}, 
      \<lbrace>\<exists>j<procs conf. part_exists \<acute>partitions p \<and> (i_partition (\<acute>locals!j)) = p \<and>                        
        (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
          part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = SYSTEM_PARTITION) \<and>
         part_mode (the (i_partition (\<acute>locals ! j)\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j)\<rbrace>,UNIV]"
apply (subgoal_tac "procs conf>0")                  
   apply (rule Parallel)              
        apply (auto simp add:   LocalRG_HoareDef.Pre_def LocalRG_HoareDef.Rely_def 
                                Com_def Guar_def Post_def Abr_def   ,
            (auto simp add: Id_def Rely_part_def Rely_part_set_mode_def )[1])
        apply (simp add: Guar_Rely_Send_ReceiveQ)         
     apply (auto simp add: Guarantee_part_def current_def )[2]
  apply (auto intro: n_n)                                               
  by (blast intro:conseqPrePost[OF Pre_union[OF conseqPrePost[OF cold_start_comp4] cold_start_comp2]])

lemma Sta_cond2'[pres]:"    
    LocalRG_HoareDef.Sta
     \<lbrace>i_partition (\<acute>locals ! i) = p \<and>      
       (part_mode (the (p\<rightarrow>\<acute>partitions)) = COLD_START \<longrightarrow>
        (\<exists>j<Sys_Config.procs conf.
            evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
            p = i_partition (\<acute>locals ! j) \<and>
            (i_partition (\<acute>locals ! j) = current (schedule (\<acute>locals ! j)) \<or>
             part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION) \<and>
            COLD_START = in_p_mode (\<acute>locals ! j)))\<rbrace>
     (Rely_part i)" 
  apply (simp add: Sta_def) apply clarsimp 
  apply auto
  apply (simp add: Rely_part_def)
     apply (erule disjE)
     apply (erule exE)
     apply (auto simp add: Rely_part_set_mode_def)[1]
    apply fastforce 
  apply (simp add: Rely_part_def)
     apply (erule disjE)
    apply (erule exE)
    apply (simp add: Rely_part_set_mode_def)  
     apply (auto simp add: Rely_part_set_mode_def)[1]
   apply fastforce 
apply (simp add: Rely_part_def)
     apply (erule disjE)
    apply (erule exE)
apply (simp add: Rely_part_set_mode_def)  
     apply (auto simp add: Rely_part_set_mode_def)[1]
  by fastforce 

lemma not_cold_start_comp4:
  " i < Sys_Config.procs conf \<Longrightarrow>
    \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> execute_service i sat [Collect part_state_conf \<inter> \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
      \<lbrace>part_mode (the (p\<rightarrow>\<acute>partitions)) \<noteq> COLD_START\<rbrace> \<inter>      
      \<lbrace>(i_partition (\<acute>locals ! i) = p \<and>
        evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
        (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION))\<rbrace>, Rely_part i, Guarantee_part i, 
       \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
       \<lbrace>(\<exists>j<Sys_Config.procs conf.
           i_partition (\<acute>locals ! j) = p \<and>
           evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
           (i_partition (\<acute>locals ! j) = current (schedule (\<acute>locals ! j)) \<or>
            part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION)) \<and>
            (i_partition (\<acute>locals ! i) = p \<and>  evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
            (i_partition (\<acute>locals ! i) = current (schedule (\<acute>locals ! i)) \<or>
             part_type (the (partition_conf conf (current (schedule (\<acute>locals ! i))))) = SYSTEM_PARTITION) \<longrightarrow> 
            (\<exists>k<Sys_Config.procs conf.
               i_partition (\<acute>locals ! k) = p \<and>   evnt (\<acute>locals ! k) = Set_Partition_Mode \<and>
              (i_partition (\<acute>locals ! k) = current (schedule (\<acute>locals ! k)) \<or>
              part_type (the (partition_conf conf (current (schedule (\<acute>locals ! k))))) = SYSTEM_PARTITION) \<and>
              part_mode (the (i_partition (\<acute>locals ! k)\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! k)))\<rbrace>,UNIV]"
   apply(rule conseqPre[of _ _ _ _ "Collect part_state_conf \<inter> 
      \<lbrace>i_partition (\<acute>locals ! i) = p \<and> 
       (part_mode (the (p\<rightarrow>\<acute>partitions)) \<noteq> COLD_START \<or>
        (\<exists>j<Sys_Config.procs conf.
            evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
            p = i_partition (\<acute>locals ! j) \<and>
            (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
              part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = SYSTEM_PARTITION) \<and>
              part_mode (the (p\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j)))\<rbrace> \<inter>      
      \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>
        \<lbrace>part_exists \<acute>partitions p \<and> (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION) \<rbrace>"], auto)     
  apply (rule conseqPrePost[OF execute_service[OF _ _ _ _ _ _ _ _ _ _ set_partition_mode_i_not_cold_p[where p="p"], 
          where  m="Set_Partition_Mode" and P="Collect part_state_conf \<inter> 
      \<lbrace>i_partition (\<acute>locals ! i) = p \<and> (part_mode (the (p\<rightarrow>\<acute>partitions)) \<noteq> COLD_START \<or>
               (\<exists>j<Sys_Config.procs conf.
                  evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
                  p = i_partition (\<acute>locals ! j) \<and>
                 (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
                     part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = 
                       SYSTEM_PARTITION) \<and>
                  part_mode (the (p\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j)))\<rbrace> \<inter>      
      \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>
        \<lbrace>part_exists \<acute>partitions p \<and> (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION) \<rbrace>"]], auto)
  apply (fastforce intro: Sta_intro pres)+
               apply (auto simp add: reflexive_Guarantee_Part)[1]
              apply (fastforce intro: Sta_intro pres)+
  by (auto simp add: current_def body)

lemma Sta_no_cond2a[pres]: "
   Sta \<lbrace>\<not>(i_partition (\<acute>locals ! i) = p \<and>
        evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
        (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION))\<rbrace> 
   (Rely_part i)"
apply (simp add: Sta_def) 
  apply (simp add: Rely_part_def Rely_part_set_mode_def)  
  by metis


lemma Sta_cond1b[pres]:"    
    LocalRG_HoareDef.Sta
     \<lbrace> (\<exists>j<Sys_Config.procs conf.
           evnt (\<acute>locals ! j) = Set_Partition_Mode \<and> 
          p = i_partition (\<acute>locals ! j) \<and>           
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION))\<rbrace>
     (Rely_part i)"
  apply (simp add: Sta_def) apply clarsimp apply (erule disjE)
  apply (simp add: Rely_part_def)  
   apply (erule disjE)
    apply (erule exE)  
    apply (simp add: Rely_part_set_mode_def)    
  apply (case_tac "part_mode (the (partitions_' x' (current (schedule (locals_' x' ! j))))) \<noteq>
       part_mode (the (partitions_' y1 (current (schedule (locals_' x' ! j)))))")
     apply metis
    apply metis 
   apply fastforce 
  apply (simp add: Rely_part_def)  
  apply (erule disjE)
   apply (erule exE)
   apply (auto simp add: Rely_part_set_mode_def)[1] 
  by fastforce


lemma exec_ivalid_not_cold1:"i < Sys_Config.procs conf \<Longrightarrow>
       part_state_conf \<lparr>locals_' = l, timer_' = t, partitions_' = part\<rparr> \<Longrightarrow>
       part_exists part p \<Longrightarrow>
       evnt (l ! i) = Set_Partition_Mode \<Longrightarrow>
       i_partition (l ! i) = p \<longrightarrow>
       p \<noteq> schedule (l ! i) \<and>
       part_type (the (partition_conf conf (schedule (l ! i)))) \<noteq> SYSTEM_PARTITION \<Longrightarrow>
       \<exists>j<Sys_Config.procs conf.
          evnt (l ! j) = Set_Partition_Mode \<and>
          p = i_partition (l ! j) \<and>
          (i_partition (l ! j) = current (schedule (l ! j)) \<or>
           part_type (the (partition_conf conf (current (schedule (l ! j))))) = SYSTEM_PARTITION) \<Longrightarrow>
       part_exists part (i_partition (l ! i)) \<Longrightarrow>
       i_partition (l ! i) = current (schedule (l ! i)) \<or>
       part_type (the (partition_conf conf (current (schedule (l ! i))))) = SYSTEM_PARTITION \<Longrightarrow>
       part_get_mutex part (i_partition (l ! i)) = 0 \<Longrightarrow>
       (Normal \<lparr>locals_' = l, timer_' = t, partitions_' = part\<rparr>,
        Normal
         \<lparr>locals_' = l, timer_' = t,
            partitions_' = part_set_mutex part (i_partition (l ! i)) (Suc i)\<rparr>)
       \<in> Guarantee_part i \<and>
       part_state_conf
        \<lparr>locals_' = l, timer_' = t,
           partitions_' = part_set_mutex part (i_partition (l ! i)) (Suc i)\<rparr> \<and>
       part_exists (part_set_mutex part (i_partition (l ! i)) (Suc i)) p \<and>
       part_exists (part_set_mutex part (i_partition (l ! i)) (Suc i))
        (i_partition (l ! i)) \<and>
       part_get_mutex (part_set_mutex part (i_partition (l ! i)) (Suc i))
        (i_partition (l ! i)) =
       Suc i"   
  apply (auto intro: set_mutex_guarantee set_mutex_part_state_conf) 
  unfolding part_exists_def part_set_mutex_def part_get_mutex_def  by auto

lemma exec_nop_not_cold:" i < Sys_Config.procs conf \<Longrightarrow>
       part_state_conf \<lparr>locals_' = l, timer_' = t, partitions_' = part\<rparr> \<Longrightarrow>
       part_exists part p \<Longrightarrow>
       evnt (l ! i) = Set_Partition_Mode \<Longrightarrow>
       i_partition (l ! i) = p \<longrightarrow>
       p \<noteq> schedule (l ! i) \<and>
       part_type (the (partition_conf conf (schedule (l ! i)))) \<noteq> SYSTEM_PARTITION \<Longrightarrow>
       \<exists>j<Sys_Config.procs conf.
          evnt (l ! j) = Set_Partition_Mode \<and>
          p = i_partition (l ! j) \<and>
          (i_partition (l ! j) = current (schedule (l ! j)) \<or>
           part_type (the (partition_conf conf (current (schedule (l ! j))))) = SYSTEM_PARTITION) \<Longrightarrow>
       part_exists part (i_partition (l ! i)) \<Longrightarrow>
       i_partition (l ! i) = current (schedule (l ! i)) \<or>
       part_type (the (partition_conf conf (current (schedule (l ! i))))) = SYSTEM_PARTITION \<Longrightarrow>
       part_get_mutex part (i_partition (l ! i)) = Suc i \<Longrightarrow>
       (part_mode (the (part (i_partition (l ! i)))) = COLD_START \<and>
        in_p_mode (l ! i) = WARM_START \<longrightarrow>
        (Normal \<lparr>locals_' = l, timer_' = t, partitions_' = part\<rparr>,
         Normal
          \<lparr>locals_' = l[i := (l ! i)\<lparr>ret_n := 0\<rparr>], timer_' = t,
             partitions_' =
               part_set_mutex part (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i)) 0\<rparr>)
        \<in> Guarantee_part i \<and>
        part_exists (part_set_mutex part (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i)) 0)
         p \<and>
        (\<exists>j<Sys_Config.procs conf.
            evnt (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j) = Set_Partition_Mode \<and>
            p = i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j) \<and>
            (i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j) =
             current (schedule (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j)) \<or>
             part_type
              (the (partition_conf conf (current (schedule (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! j))))) =
             SYSTEM_PARTITION)) \<and>
        (evnt (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i) = Set_Partition_Mode \<longrightarrow>
         i_partition (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i) = p \<longrightarrow>
         p \<noteq> schedule (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i) \<and>
         part_type (the (partition_conf conf (schedule (l[i := (l ! i)\<lparr>ret_n := 0\<rparr>] ! i)))) \<noteq>
         SYSTEM_PARTITION)) \<and>
       ((part_mode (the (part (i_partition (l ! i)))) = COLD_START \<longrightarrow>
         in_p_mode (l ! i) \<noteq> WARM_START) \<longrightarrow>
        (Normal \<lparr>locals_' = l, timer_' = t, partitions_' = part\<rparr>,
         Normal
          \<lparr>locals_' = l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>], timer_' = t,
             partitions_' =
               part_set_mutex
                (part_set_restart
                  (part_set_mode part (i_partition (l ! i)) (in_p_mode (l ! i)))
                  (i_partition (l ! i)) (in_r_mode (l ! i)))
                (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0\<rparr>)
        \<in> Guarantee_part i \<and>
        part_exists
         (part_set_mutex
           (part_set_restart (part_set_mode part (i_partition (l ! i)) (in_p_mode (l ! i)))
             (i_partition (l ! i)) (in_r_mode (l ! i)))
           (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0)
         p \<and>
        (\<exists>j<Sys_Config.procs conf.
            evnt (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j) = Set_Partition_Mode \<and>
            p = i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j) \<and>
            (i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j) =
             current (schedule (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j)) \<or>
             part_type
              (the (partition_conf conf
                     (current (schedule (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! j))))) =
             SYSTEM_PARTITION)) \<and>
        (evnt (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i) = Set_Partition_Mode \<longrightarrow>
         i_partition (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i) = p \<longrightarrow>
         p \<noteq> schedule (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i) \<and>
         part_type (the (partition_conf conf (schedule (l[i := (l ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)))) \<noteq>
         SYSTEM_PARTITION))"
apply (rule conjI)
   apply clarify
   apply (rule conjI)
    apply (drule set_v_guarantee,simp+)
apply (rule conjI)+
  apply (auto simp add:  part_exists_def part_set_mutex_def  part_set_restart_def part_set_mode_def)[1]
   apply (rule conjI)+
  apply (metis current_def nth_list_update_neq) 
   apply (auto simp: part_state_conf_def)[1] 
  apply clarify
  apply (rule conjI)
   apply (frule set_v_guarantee',simp+)
  apply (rule conjI)
   apply (auto simp add: part_exists_def part_set_mutex_def  part_set_restart_def part_set_mode_def)[1]
  apply (rule conjI)
  apply (metis (no_types) current_def nth_list_update_neq)
  by (auto simp: part_state_conf_def)[1] 

lemma not_cold_start_comp2':
  " i < Sys_Config.procs conf \<Longrightarrow>
    \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> set_partition_mode_system i 
    sat [Collect part_state_conf \<inter> \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter> \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>         
      \<lbrace>\<not>(i_partition (\<acute>locals ! i) = p \<and>
        evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
        (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION))\<rbrace> \<inter>                       
      \<lbrace>\<exists>j<Sys_Config.procs conf.
           evnt (\<acute>locals ! j) = Set_Partition_Mode \<and> 
          p = i_partition (\<acute>locals ! j) \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION)\<rbrace>, 
       Rely_part i, Guarantee_part i, 
       \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
       \<lbrace>\<exists>j<Sys_Config.procs conf.
            evnt (\<acute>locals ! j) = Set_Partition_Mode \<and> 
          p = i_partition (\<acute>locals ! j) \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION)\<rbrace> \<inter>
        \<lbrace>\<not>(i_partition (\<acute>locals ! i) = p \<and>
        evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
        (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION))\<rbrace>,UNIV]"
  unfolding set_partition_mode_system_def set_partition_mode_def Let_def  
  apply (rule If)  apply (fastforce intro: Sta_intro pres)+  apply(auto simp add: reflexive_Guarantee_Part )[1]
apply (rule Seq[of  _ _ _ _ _ _ _ _ "Collect part_state_conf \<inter> \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter> \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter>       
      \<lbrace>\<not>(i_partition (\<acute>locals ! i) = p \<and>
        evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
        (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION))\<rbrace> \<inter>                       
      \<lbrace>\<exists>j<Sys_Config.procs conf.
           evnt (\<acute>locals ! j) = Set_Partition_Mode \<and> 
          p = i_partition (\<acute>locals ! j) \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION)\<rbrace>  \<inter>
      \<lbrace>part_exists \<acute>partitions (i_partition (\<acute>locals ! i)) \<and>
       (i_partition (\<acute>locals ! i) = current (schedule (\<acute>locals ! i)) \<or>
        part_type ((the \<circ> partition_conf conf \<circ> current \<circ> schedule) (\<acute>locals ! i)) = SYSTEM_PARTITION)\<rbrace> \<inter>
                           \<lbrace>part_get_mutex \<acute>partitions (i_partition (\<acute>locals ! i)) = (Suc i)\<rbrace>"]) 
apply (fastforce intro: Sta_intro pres)+                             
  apply (auto simp only: reflexive_Guarantee_Part)  
  apply (rule Await) 
apply (fastforce intro: Sta_intro pres)+ 
    apply vcg apply simp  apply (frule exec_ivalid_not_cold1,blast+)  
apply (rule Await) apply (fastforce intro: Sta_intro pres)+  
   apply vcg apply simp apply (simp add: exec_nop_not_cold)
  apply (rule Basic)    
     apply (fastforce intro: Sta_intro pres)+
   apply (auto simp add: Guarantee_part_def Guarantee_part_set_mode_def part_state_conf_def)[1]  
  apply clarify
  apply (simp add: part_state_conf_def)
  by (metis (no_types)  nth_list_update_neq)

lemma not_cold_start_comp2'':
  " i < Sys_Config.procs conf \<Longrightarrow>
    \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> get_partition_status i 
    sat [Collect part_state_conf \<inter> \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>   
      \<lbrace>\<not>(i_partition (\<acute>locals ! i) = p \<and>
        evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
        (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION))\<rbrace> \<inter>                       
      \<lbrace>\<exists>j<Sys_Config.procs conf.
           evnt (\<acute>locals ! j) = Set_Partition_Mode \<and> 
          p = i_partition (\<acute>locals ! j) \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION)\<rbrace> \<inter>
      \<lbrace>evnt (\<acute>locals ! i) = Get_Partition_Status\<rbrace>, 
       Rely_part i, Guarantee_part i, 
       \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
       \<lbrace>\<exists>j<Sys_Config.procs conf.
            evnt (\<acute>locals ! j) = Set_Partition_Mode \<and> 
          p = i_partition (\<acute>locals ! j) \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION)\<rbrace> \<inter>
        \<lbrace>\<not>(i_partition (\<acute>locals ! i) = p \<and>
        evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
        (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION))\<rbrace>,UNIV]"
  unfolding get_partition_status_def Let_def  
apply (rule Basic)  
     apply (fastforce intro: Sta_intro pres)+
   apply (auto simp add: Guarantee_part_def Guarantee_part_get_state_def part_state_conf_def)[1]  
  apply clarify
  apply (simp add: part_state_conf_def) 
  by (metis (no_types, lifting) Evnt.distinct(67) nth_list_update_neq)

lemma not_cold_start_comp2:
  " i < Sys_Config.procs conf \<Longrightarrow>
    \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> execute_service i 
    sat [Collect part_state_conf \<inter> \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
      \<lbrace>part_mode (the (p\<rightarrow>\<acute>partitions)) \<noteq> COLD_START\<rbrace> \<inter>      
      \<lbrace>\<not>(i_partition (\<acute>locals ! i) = p \<and>
        evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
        (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION))\<rbrace> \<inter>                       
      \<lbrace>\<exists>j<Sys_Config.procs conf.
          i_partition (\<acute>locals ! j) = p \<and>
          evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>         
          (i_partition (\<acute>locals ! j) = current (schedule (\<acute>locals ! j)) \<or>
           part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) =
           SYSTEM_PARTITION)\<rbrace>, Rely_part i, Guarantee_part i, 
       \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
       \<lbrace>(\<exists>j<Sys_Config.procs conf.
           i_partition (\<acute>locals ! j) = p \<and>
           evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
           (i_partition (\<acute>locals ! j) = current (schedule (\<acute>locals ! j)) \<or>
            part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION)) \<and>
            (i_partition (\<acute>locals ! i) = p \<and>  evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
            (i_partition (\<acute>locals ! i) = current (schedule (\<acute>locals ! i)) \<or>
             part_type (the (partition_conf conf (current (schedule (\<acute>locals ! i))))) = SYSTEM_PARTITION) \<longrightarrow> 
            (\<exists>k<Sys_Config.procs conf.
               i_partition (\<acute>locals ! k) = p \<and>   evnt (\<acute>locals ! k) = Set_Partition_Mode \<and>
              (i_partition (\<acute>locals ! k) = current (schedule (\<acute>locals ! k)) \<or>
              part_type (the (partition_conf conf (current (schedule (\<acute>locals ! k))))) = SYSTEM_PARTITION) \<and>
              part_mode (the (i_partition (\<acute>locals ! k)\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! k)))\<rbrace>,UNIV]"
apply (rule conseqPrePost[of _ _ _ _ "Collect part_state_conf \<inter> \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>         
      \<lbrace>\<not>(i_partition (\<acute>locals ! i) = p \<and>
        evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
        (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION))\<rbrace> \<inter>                       
      \<lbrace>\<exists>j<Sys_Config.procs conf.
           evnt (\<acute>locals ! j) = Set_Partition_Mode \<and> 
          p = i_partition (\<acute>locals ! j) \<and>          
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION)\<rbrace>" "Rely_part i" "Guarantee_part i"
     "\<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
       \<lbrace>\<exists>j<Sys_Config.procs conf.
            evnt (\<acute>locals ! j) = Set_Partition_Mode \<and> 
          p = i_partition (\<acute>locals ! j) \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION)\<rbrace> \<inter>
        \<lbrace>\<not>(i_partition (\<acute>locals ! i) = p \<and>
        evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
        (i_partition (\<acute>locals ! i) = schedule (\<acute>locals ! i) \<or>
         part_type (the (partition_conf conf (schedule (\<acute>locals ! i)))) = SYSTEM_PARTITION))\<rbrace>"])  
  unfolding execute_service_def
  apply (rule If)  
      apply (fastforce intro: Sta_intro pres)
     apply(auto simp add: reflexive_Guarantee_Part )[1]
    apply (rule Call)
       apply (fastforce intro: Sta_intro pres)
      apply(auto simp add: reflexive_Guarantee_Part )[1]
         apply ( auto simp add: body)[2]
  apply (blast intro:  conseqPrePost[OF not_cold_start_comp2''])
    apply (rule If)  
          apply (fastforce intro: Sta_intro pres)
         apply(auto simp add: reflexive_Guarantee_Part )[1]
    apply (rule Call)
       apply (fastforce intro: Sta_intro pres)
      apply(auto simp add: reflexive_Guarantee_Part )[1]
         apply ( auto simp add: body)[2]
        apply (blast intro:  conseqPrePost[OF not_cold_start_comp2'])
       apply (rule conseqPre) 
        apply (rule Skip)
         apply (fastforce intro: Sta_intro pres)
by (auto simp add: current_def reflexive_Guarantee_Part)


lemma Part_not_cold:
"\<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> 
  (COBEGIN SCHEME [0 \<le> i < procs conf]
  (execute_service i, 
    Collect part_state_conf \<inter> 
      \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
      \<lbrace>part_mode (the (\<acute>partitions  p)) \<noteq> COLD_START\<rbrace> \<inter>
      \<lbrace>\<exists>j. j< procs conf \<and> 
        (i_partition (\<acute>locals!j)) = p \<and> 
        evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>                                     
        (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
          part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = SYSTEM_PARTITION)\<rbrace>,  
      Rely_part i, Guarantee_part  i, 
      \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter> 
        \<lbrace>(\<exists>j< procs conf.
          (i_partition (\<acute>locals!j)) = p \<and>                 
          evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
          (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
          part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = SYSTEM_PARTITION)) \<and>
         (((i_partition (\<acute>locals!i)) = p \<and>                 
          evnt (\<acute>locals ! i) = Set_Partition_Mode \<and>
          (i_partition (\<acute>locals!i) = (current (schedule (\<acute>locals!i))) \<or> 
          part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!i)) = SYSTEM_PARTITION)) \<longrightarrow> 
            (\<exists>k< procs conf.
              i_partition (\<acute>locals!k) = p \<and>
              evnt (\<acute>locals ! k) = Set_Partition_Mode \<and>
             (i_partition (\<acute>locals!k) = (current (schedule (\<acute>locals!k))) \<or> 
              part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!k)) = SYSTEM_PARTITION) \<and> 
              part_mode (the (i_partition (\<acute>locals ! k)\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! k))) 
                \<rbrace>,UNIV)
  COEND)
  SAT [{s. part_state_conf s} \<inter> \<lbrace>part_exists \<acute>partitions p\<rbrace> \<inter>
      \<lbrace>part_mode (the (\<acute>partitions  p))\<noteq> COLD_START\<rbrace> \<inter>
       \<lbrace>\<exists>j. j<procs conf \<and> 
       (i_partition (\<acute>locals!j)) = p \<and>        
       evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>                             
        (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
            part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = SYSTEM_PARTITION)\<rbrace>, 
      Id, {(x,y). \<exists>nx ny. x=Normal nx \<and> y=Normal ny}, 
      \<lbrace>\<exists>j<procs conf. part_exists \<acute>partitions p \<and> (i_partition (\<acute>locals!j)) = p \<and>                        
        (i_partition (\<acute>locals!j) = (current (schedule (\<acute>locals!j))) \<or> 
          part_type ((the o partition_conf conf o current o schedule) (\<acute>locals!j)) = SYSTEM_PARTITION) \<and>
         part_mode (the (i_partition (\<acute>locals ! j)\<rightarrow>\<acute>partitions)) = in_p_mode (\<acute>locals ! j)\<rbrace>,UNIV]"
apply (subgoal_tac "procs conf>0")                  
   apply (rule Parallel)              
        apply (auto simp add:   LocalRG_HoareDef.Pre_def LocalRG_HoareDef.Rely_def 
                                Com_def Guar_def Post_def Abr_def   ,
            (auto simp add: Id_def Rely_part_def Rely_part_set_mode_def )[1])
        apply (simp add: Guar_Rely_Send_ReceiveQ)         
     apply (auto simp add: Guarantee_part_def current_def )[2]
  apply (auto intro: n_n)                                               
  by (blast intro:conseqPrePost[OF Pre_union[OF conseqPrePost[OF not_cold_start_comp4] not_cold_start_comp2]])

lemma set_partition_mode_unique_not_system_self:
  "i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> set_partition_mode_system i sat [
            \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode \<rbrace> \<inter>   
             \<lbrace>(\<forall>j<Sys_Config.procs conf.
                              i_partition (\<acute>locals ! i) = i_partition (\<acute>locals ! j) \<and>
                              evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
                              i_partition (\<acute>locals ! j) \<noteq> current (schedule (\<acute>locals ! j)) \<and>
                              part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) \<noteq>
                              SYSTEM_PARTITION \<and>
                              \<not> part_exists \<acute>partitions (i_partition (\<acute>locals ! j))) \<and>
                          i_partition (\<acute>locals ! i)\<rightarrow>\<acute>partitions = p\<rbrace>,  
            Rely_part i, 
            Guarantee_part  i, 
             \<lbrace>evnt (\<acute>locals ! i) = Set_Partition_Mode\<rbrace> \<inter> 
              \<lbrace>(\<forall>j<Sys_Config.procs conf.
                              i_partition (\<acute>locals ! i) = i_partition (\<acute>locals ! j) \<and>
                              evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
                              i_partition (\<acute>locals ! j) \<noteq> current (schedule (\<acute>locals ! j)) \<and>
                              part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) \<noteq>
                              SYSTEM_PARTITION \<and>
                              \<not> part_exists \<acute>partitions (i_partition (\<acute>locals ! j))) \<and>
                          i_partition (\<acute>locals ! i)\<rightarrow>\<acute>partitions = p\<rbrace>,UNIV]"
    unfolding set_partition_mode_system_def set_partition_mode_def Let_def  
  apply (rule If, auto simp add: reflexive_Guarantee_Part)
      apply (fastforce intro: Sta_intro pres)+  
  apply (simp add: b1  False_sat)    
    apply (rule Basic) 
       apply (fastforce intro: Sta_intro pres)
    apply(fastforce intro: Sta_intro pres)
  apply (blast intro:modify_ret_guarantee)     
    apply (simp only:CollInt_iff)
    apply clarify
    by (metis  modify_ret_eq_vars)

lemma get_partition_status_eq_i_partition:
  "i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> get_partition_status i sat [
            {s. part_state_conf s} \<inter> \<lbrace>i_partition (\<acute>locals!i) = p\<rbrace> \<inter> \<lbrace>evnt (\<acute>locals !i) = Get_Partition_Status\<rbrace>,  
            Rely_part i, 
            Guarantee_part  i, 
            {s. part_state_conf s} \<inter> \<lbrace>i_partition (\<acute>locals!i) = p\<rbrace> \<inter> \<lbrace>evnt (\<acute>locals !i) = Get_Partition_Status\<rbrace>,UNIV]"
  unfolding get_partition_status_def Let_def          
    apply (rule Basic) 
       apply (fastforce intro: Sta_intro pres)+   
  unfolding Guarantee_part_def Guarantee_part_get_state_def part_state_conf_def 
  by auto

lemma execute_service_eq_i_partition:
  "i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> execute_service i sat [
            {s. part_state_conf s} \<inter> \<lbrace>i_partition (\<acute>locals!i) = p\<rbrace>,  
            Rely_part i, 
            Guarantee_part  i, 
            {s. part_state_conf s} \<inter> \<lbrace>i_partition (\<acute>locals!i) = p\<rbrace>,UNIV]"
  unfolding execute_service_def Let_def          
    apply (rule If) 
     apply (fastforce intro: Sta_intro pres)+   
    apply (auto simp add: reflexive_Guarantee_Part)[1]
   apply (rule Call)
      apply (fastforce intro: Sta_intro pres)
     apply(auto simp add: reflexive_Guarantee_Part )[1]
    apply ( auto simp add: body)[2]
   apply (blast intro:  conseqPrePost[OF get_partition_status_eq_i_partition])
apply (rule If) 
     apply (fastforce intro: Sta_intro pres)+   
    apply (auto simp add: reflexive_Guarantee_Part)[1]
   apply (rule Call)
      apply (fastforce intro: Sta_intro pres)
     apply(auto simp add: reflexive_Guarantee_Part )[1]
    apply ( auto simp add: body)[2]
   apply (blast intro:  conseqPrePost[OF set_partition_mode_eq_i_partition])
  apply (rule conseqPre) 
   apply (rule Skip)
    apply (fastforce intro: Sta_intro pres)
by (auto simp add: reflexive_Guarantee_Part)


lemma get_partition_status_unique_not_system_self:
  "i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> get_partition_status i sat [
            \<lbrace>evnt (\<acute>locals ! i) = Get_Partition_Status \<rbrace> \<inter>   
             \<lbrace>(\<forall>j<Sys_Config.procs conf.
                              i_partition (\<acute>locals ! i) = i_partition (\<acute>locals ! j) \<and>
                              evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
                              i_partition (\<acute>locals ! j) \<noteq> current (schedule (\<acute>locals ! j)) \<and>
                              part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) \<noteq>
                              SYSTEM_PARTITION \<and>
                              \<not> part_exists \<acute>partitions (i_partition (\<acute>locals ! j))) \<and>
                          i_partition (\<acute>locals ! i)\<rightarrow>\<acute>partitions = p\<rbrace>,  
            Rely_part i, 
            Guarantee_part  i, 
             \<lbrace>evnt (\<acute>locals ! i) = Get_Partition_Status\<rbrace> \<inter> 
              \<lbrace>(\<forall>j<Sys_Config.procs conf.
                              i_partition (\<acute>locals ! i) = i_partition (\<acute>locals ! j) \<and>
                              evnt (\<acute>locals ! j) = Set_Partition_Mode \<and>
                              i_partition (\<acute>locals ! j) \<noteq> current (schedule (\<acute>locals ! j)) \<and>
                              part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) \<noteq>
                              SYSTEM_PARTITION \<and>
                              \<not> part_exists \<acute>partitions (i_partition (\<acute>locals ! j))) \<and>
                          i_partition (\<acute>locals ! i)\<rightarrow>\<acute>partitions = p\<rbrace>,UNIV]"
    unfolding get_partition_status_def Let_def          
    apply (rule Basic) 
       apply (fastforce intro: Sta_intro pres)
    apply(fastforce intro: Sta_intro pres)     
    apply clarify
     apply (metis Evnt.distinct(67))
    apply clarify
    by (metis Evnt.distinct(67))

lemma execute_service_unique_not_system_self:
  "i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> execute_service i sat [   
             \<lbrace>\<not>(\<exists>j. j < procs conf \<and>  
                  (i_partition (\<acute>locals!i) = i_partition (\<acute>locals!j) \<and> evnt (\<acute>locals ! j) = Set_Partition_Mode \<longrightarrow>
                   (i_partition (\<acute>locals ! j) = current (schedule (\<acute>locals ! j)) \<or>
                    part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION) \<or> 
                   part_exists \<acute>partitions (i_partition (\<acute>locals ! i)))) \<and>
              \<acute>partitions (i_partition (\<acute>locals!i)) = p\<rbrace>,  
            Rely_part i, 
            Guarantee_part  i,               
              \<lbrace>\<not>(\<exists>j. j < procs conf \<and>  
                  (i_partition (\<acute>locals!i) = i_partition (\<acute>locals!j)\<and>evnt (\<acute>locals ! j) = Set_Partition_Mode \<longrightarrow>
                   (i_partition (\<acute>locals ! j) = current (schedule (\<acute>locals ! j)) \<or>
                    part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION) \<or> 
                   part_exists \<acute>partitions (i_partition (\<acute>locals ! i)))) \<and> 
             \<acute>partitions (i_partition (\<acute>locals!i)) = p\<rbrace>,UNIV]"
  unfolding execute_service_def Let_def          
    apply (rule If) 
     apply (fastforce intro: Sta_intro pres)+   
    apply (auto simp add: reflexive_Guarantee_Part)[1]
   apply (rule Call)
      apply (fastforce intro: Sta_intro pres)
     apply(auto simp add: reflexive_Guarantee_Part )[1]
    apply ( auto simp add: body)[2]    
   apply (blast intro:  conseqPrePost[OF get_partition_status_unique_not_system_self])
apply (rule If) 
     apply (fastforce intro: Sta_intro pres)+   
    apply (auto simp add: reflexive_Guarantee_Part)[1]
   apply (rule Call)
      apply (fastforce intro: Sta_intro pres)
     apply(auto simp add: reflexive_Guarantee_Part )[1]
    apply ( auto simp add: body)[2]
   apply (auto intro:  conseqPrePost[OF set_partition_mode_unique_not_system_self])
  apply (rule conseqPre) 
   apply (rule Skip)
    apply (fastforce intro: Sta_intro pres)
by (auto simp add: reflexive_Guarantee_Part)

lemma set_partition_mode_unique_not_system_self_p:
  "i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> execute_service i sat [
            {s. part_state_conf s} \<inter> 
             \<lbrace>i_partition (\<acute>locals!i) = p \<and>
              \<not>(\<exists>j. j < procs conf \<and>  
                  (p = i_partition (\<acute>locals!j) \<and> evnt (\<acute>locals ! j) = Set_Partition_Mode \<longrightarrow>
                   (i_partition (\<acute>locals ! j) = current (schedule (\<acute>locals ! j)) \<or>
                    part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION) \<or> 
                   part_exists \<acute>partitions (i_partition (\<acute>locals ! i)))) \<and>
              \<acute>partitions p = pa\<rbrace>,  
            Rely_part i, 
            Guarantee_part  i,               
              \<lbrace>i_partition (\<acute>locals!i) = p \<and> 
               \<not>(\<exists>j. j < procs conf \<and>  
                  (p = i_partition (\<acute>locals!j)\<and>evnt (\<acute>locals ! j) = Set_Partition_Mode \<longrightarrow>
                   (i_partition (\<acute>locals ! j) = current (schedule (\<acute>locals ! j)) \<or>
                    part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION) \<or> 
                   part_exists \<acute>partitions (i_partition (\<acute>locals ! i)))) \<and> 
             \<acute>partitions p = pa\<rbrace>,UNIV]"
  by (blast intro: conseqPrePost inter_pre_post[OF execute_service_unique_not_system_self[where p=pa] 
                    execute_service_eq_i_partition[where p=p]])


lemma Part_not_conds:
"\<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> 
  (COBEGIN SCHEME [0 \<le> i < procs conf]
  (execute_service i, 
    Collect part_state_conf \<inter>                  
        \<lbrace>(i_partition (\<acute>locals!i)) = p\<rbrace> \<inter>
      \<lbrace>\<not>(\<exists>j. j < procs conf \<and>  
            (p = i_partition (\<acute>locals!j) \<and> evnt (\<acute>locals ! j) = Set_Partition_Mode \<longrightarrow>
             (i_partition (\<acute>locals ! j) = current (schedule (\<acute>locals ! j)) \<or>
              part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION) \<or> 
             part_exists \<acute>partitions (i_partition (\<acute>locals ! i)))) \<and> \<acute>partitions p = pa\<rbrace>,  
      Rely_part i, Guarantee_part  i, 
        \<lbrace>\<not>(\<exists>j. j < procs conf \<and>  
            (p = i_partition (\<acute>locals!j) \<and> evnt (\<acute>locals ! j) = Set_Partition_Mode \<longrightarrow>
             (i_partition (\<acute>locals ! j) = current (schedule (\<acute>locals ! j)) \<or>
              part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION) \<or> 
             part_exists \<acute>partitions (i_partition (\<acute>locals ! i)))) \<and> \<acute>partitions p = pa \<rbrace>,UNIV)
  COEND)
  SAT [{s. part_state_conf s} \<inter> 
       \<lbrace>\<not>(\<exists>j. j < procs conf \<and>  
            (p = i_partition (\<acute>locals!j) \<and> evnt (\<acute>locals ! j) = Set_Partition_Mode \<longrightarrow>
             (i_partition (\<acute>locals ! j) = current (schedule (\<acute>locals ! j)) \<or>
              part_type (the (partition_conf conf (current (schedule (\<acute>locals ! j))))) = SYSTEM_PARTITION) \<or> 
             part_exists \<acute>partitions p))\<rbrace> \<inter>
       \<lbrace>\<acute>partitions p = pa\<rbrace>, 
      Id, {(x,y). \<exists>nx ny. x=Normal nx \<and> y=Normal ny}, 
      \<lbrace> \<acute>partitions p = pa\<rbrace>,UNIV]"
apply (subgoal_tac "procs conf>0")                  
   apply (rule Parallel)              
        apply (auto simp add:   LocalRG_HoareDef.Pre_def LocalRG_HoareDef.Rely_def 
                                Com_def Guar_def Post_def Abr_def   ,
            (auto simp add: Id_def Rely_part_def Rely_part_set_mode_def )[1])
        apply (simp add: Guar_Rely_Send_ReceiveQ)         
     apply (auto simp add: Guarantee_part_def current_def )[2]
  apply (auto intro: n_n)                                               
  by (blast intro:conseqPrePost[OF set_partition_mode_unique_not_system_self_p])



end
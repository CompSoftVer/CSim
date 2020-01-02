theory ArincRefinement
  imports "../Communication/Spec/ArincSpecQueue" "../Communication/Impl/ArincImp" "CSim.Sim_Rules"
begin

lemma id_R_rtrancl_trancl:"\<forall>a. (a,a)\<in>R \<Longrightarrow> R\<^sup>*=R\<^sup>+"
  by (metis equalityI prod.exhaust r_into_rtrancl r_into_trancl' subsetI trancl_rtrancl_absorb transitive_closure_trans(8))


definition Stap::"'s set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> bool" 
  where 
 "Stap \<equiv> \<lambda>f g. (\<forall>x y. x \<in> f  \<longrightarrow>  (x,y)\<in> g \<longrightarrow>  y \<in> f)"

lemma Sta1:"Stap f R \<Longrightarrow> R `` f \<subseteq> f"
  unfolding Stap_def by auto

lemma Sta2:"R `` f \<subseteq> f \<Longrightarrow> Stap f R"
  unfolding Stap_def by auto

lemma Sta3:"Stap f R = (R `` f \<subseteq> f)"
  using Sta1 Sta2 by auto

lemma "R `` P \<subseteq> P \<Longrightarrow> R\<^sup>* `` P = P"
  by (simp add: Image_closed_trancl)

lemma "Stap f R \<Longrightarrow> Stap f (R\<^sup>*)"
   by (simp add: Sta3 Image_closed_trancl)

(* lemma "R\<subseteq>\<alpha>\<^sub>x \<Longrightarrow> Sta R p"
  sorry
lemma "(\<forall>a b c. (a,b)\<in>R \<and> (b,c)\<in>R  \<longrightarrow> (a,c)\<in>R) \<Longrightarrow> R = R\<^sup>+"
  sorry
lemma "ArincQueuing.Rely_Send_ReceiveQ i = (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*"
  sorry *)
lemma rely_rtrancl_trancl[simp]:"(ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>* = (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+"
  using id_R_rtrancl_trancl reflexive_rely_send   
  by (simp add: id_R_rtrancl_trancl reflexive_rely_send) 

lemma rely_normal_tran:
"(x,y) \<in> (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+ \<Longrightarrow>
 x = Normal x1 \<Longrightarrow>
 \<exists>y1. y = Normal y1"
proof (induct rule:trancl_induct)
case (base y)
  then show ?case unfolding ArincQueuing.Rely_Send_ReceiveQ_def by auto
next
  case (step y z)
  then show ?case  unfolding ArincQueuing.Rely_Send_ReceiveQ_def by auto 
qed

lemma imp_rely_normal_tran:
"(Normal x1 ,y) \<in> (ArincImp.Rely_Send_ReceiveQ i) \<Longrightarrow> 
 \<exists>y1. y = Normal y1"
unfolding ArincImp.Rely_Send_ReceiveQ_def by auto

lemma imp_rely_alpha_x:"Rely_Send_ReceiveQ i \<subseteq> \<alpha>\<^sub>x "
  unfolding alpha_xstate_def Rely_Send_ReceiveQ_def by auto

lemma spec_rely_alpha_x: "ArincQueuing.Rely_Send_ReceiveQ i \<subseteq> \<alpha>\<^sub>x"
  unfolding alpha_xstate_def ArincQueuing.Rely_Send_ReceiveQ_def by auto

lemma spec_rely_alpha_x_tran1:"(a, b) \<in> (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+ \<Longrightarrow> (a, b) \<in> \<alpha>\<^sub>x"    
proof (induct rule:trancl_induct)
case (base y)
  then show ?case using spec_rely_alpha_x by auto
next
  case (step y z)
  then show ?case using spec_rely_alpha_x
    using alpha_x_tran by blast  
qed

lemma spec_rely_alpha_x_tran: "(ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+ \<subseteq> \<alpha>\<^sub>x"
  using spec_rely_alpha_x_tran1 by auto



definition Sta\<^sub>sS :: "('s,'s1) invs \<Rightarrow> 
                   ((('s,'f) xstate\<times>('s,'f) xstate)\<times>(('s1,'f) xstate\<times>('s1,'f) xstate)) set \<Rightarrow> bool" where
  "Sta\<^sub>sS f R \<equiv>  (\<forall>x x1 y y1. (x,y) \<in> f \<and>  ((Normal x, Normal x1),Normal y,Normal y1)\<in> R \<longrightarrow> (x1,y1)\<in> f)  "

lemma stable_related':"Sta\<^sub>sS f (R1, R2')\<^sub>f "
  unfolding Sta\<^sub>sS_def related_transitions_def by fastforce

lemma eq_sta:"R \<subseteq> \<alpha>\<^sub>x \<Longrightarrow> (R1\<^sup>+) \<subseteq>\<alpha>\<^sub>x \<Longrightarrow> Sta\<^sub>sS P ((R,R1\<^sup>+)\<^sub>\<alpha>) = (Sta\<^sub>s P (R,R1\<^sup>+)\<^sub>\<alpha>)"
  unfolding Sta\<^sub>s_def Sta\<^sub>sS_def alpha_xstate_def related_transitions_def
  apply clarsimp 
  by blast


lemma eq_related_tran[simp]: "Sta\<^sub>sS P (((Rely_Send_ReceiveQ i)::(('a vars_scheme, 'b) xstate \<times> ('a vars_scheme, 'b) xstate) set,
                                  ((ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+))\<^sub>\<alpha>) =
                       (Sta\<^sub>s P ((Rely_Send_ReceiveQ i)::(('a vars_scheme, 'b) xstate \<times> ('a vars_scheme, 'b) xstate) set,
                       ((ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+))\<^sub>\<alpha>)"
  using eq_sta[OF imp_rely_alpha_x spec_rely_alpha_x_tran] by auto

lemma stable_related:"Sta\<^sub>s f ((Rely_Send_ReceiveQ i), ((ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+))\<^sub>f"    
  using eq_related_tran stable_related' by blast 
  
  

lemma rtranclp_trans_induct:
  assumes major: "r\<^sup>*\<^sup>* x y"
    and cases: "\<And>x. P x x" "\<And>x y. r x y \<Longrightarrow> P x y" "\<And>x y z. r\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> r\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
  shows "P x y"
proof-
  have "x=y \<or> (x\<noteq>y \<and> r\<^sup>+\<^sup>+ x y)" using rtranclpD[OF major] by auto
  moreover {assume "x=y" 
    then have ?thesis using cases by auto}
  moreover
  {assume "x\<noteq>y \<and> r\<^sup>+\<^sup>+ x y" 
    then have r:"r\<^sup>+\<^sup>+ x y" by auto
    then have ?thesis using  tranclp_trans_induct[OF r] using cases by blast
  }
  ultimately show ?thesis by auto
qed

lemmas rtrancl_trans_induct = rtranclp_trans_induct [to_set]

lemma Sta_dest:"Sta f R \<Longrightarrow> 
                x\<in>f \<Longrightarrow>
                (Normal x, y) \<in>R \<Longrightarrow>
                \<exists>y'. y = Normal y' \<and> y' \<in> f"
  unfolding Sta_def
  by auto

lemma eq_sta\<^sub>s_pre: "Sta\<^sub>s P (R, R')\<^sub>a \<Longrightarrow> P = P' \<Longrightarrow> Sta\<^sub>s P' (R, R')\<^sub>a"
  by auto

lemma eq_sta\<^sub>s_preS: "Sta\<^sub>sS P (R, R')\<^sub>a \<Longrightarrow> P = P' \<Longrightarrow> Sta\<^sub>sS P' (R, R')\<^sub>a"
  by auto

 lemma Sta_\<^sub>s: "Sta A R \<Longrightarrow>
       Sta B  (R'\<^sup>*) \<Longrightarrow>
       Sta\<^sub>sS {(\<sigma>,\<Sigma>). \<sigma>\<in>A \<and> \<Sigma>\<in>B} (R, R'\<^sup>*)\<^sub>a"
   unfolding Sta_def Sta\<^sub>sS_def related_transitions_def    
   by auto

lemma in_image_Pred:"(\<sigma>,\<Sigma>)\<in>a \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow> Q = a `` P \<Longrightarrow> \<Sigma> \<in> Q"
  by auto

lemma sta_in_image_sta\<^sub>s: "Sta P R \<Longrightarrow> Q = a `` P \<Longrightarrow> Sta\<^sub>sS (P\<odot>Q) (R, R')\<^sub>a"
   unfolding Sta_def Sta\<^sub>sS_def related_transitions_def and_rel_def
   by auto

lemma Sta_s_sta_l_intro:"Sta P R \<Longrightarrow> Sta\<^sub>sS (P\<odot>UNIV) (R, R')\<^sub>a"
   unfolding Sta_def Sta\<^sub>sS_def related_transitions_def and_rel_def
   by auto

lemma Sta_s_sta_r_intro:"Sta Q R' \<Longrightarrow> Sta\<^sub>sS (UNIV\<odot>Q) (R, R')\<^sub>a"
   unfolding Sta_def Sta\<^sub>sS_def related_transitions_def and_rel_def
   by auto

lemma Sta_s_sta_intro1:"Sta P R \<Longrightarrow> Sta Q R' \<Longrightarrow> Sta\<^sub>sS (P\<odot>Q) (R, R')\<^sub>a"
   unfolding Sta_def Sta\<^sub>sS_def related_transitions_def and_rel_def
   by fastforce

lemma Sta_s_sta_intro:"Sta P R \<Longrightarrow> Sta Q R' \<Longrightarrow> Sta\<^sub>sS ({(x,y). x\<in>P} \<inter> {(x,y). y\<in>Q}) (R, R')\<^sub>a"
   unfolding Sta_def Sta\<^sub>sS_def related_transitions_def and_rel_def
   by fastforce

lemma Sta_s_sta_intro':"Sta P R \<Longrightarrow> Sta Q R' \<Longrightarrow> Sta\<^sub>sS ({(x,y). x\<in>P \<and> y\<in>Q}) (R, R')\<^sub>a"
   unfolding Sta_def Sta\<^sub>sS_def related_transitions_def and_rel_def
   by fastforce

lemma sta_s_int_ex:"(\<And>i. Sta (P i) R) \<Longrightarrow> (\<And>i. Sta (Q i) R') \<Longrightarrow> Sta\<^sub>sS ({(\<sigma>,\<Sigma>). (\<exists>i. \<sigma>\<in>(P i) \<and> \<Sigma>\<in> (Q i))}) (R, R')\<^sub>a"
   unfolding Sta_def Sta\<^sub>sS_def related_transitions_def 
   by fast

lemma sta_s_inter_intro: "Sta\<^sub>sS (P1\<odot>Q1) (R, R')\<^sub>a \<Longrightarrow> 
                          Sta\<^sub>sS (P2\<odot>Q2) (R, R')\<^sub>a \<Longrightarrow> 
                          Sta\<^sub>sS ((P1 \<inter> P2)  \<odot> (Q1 \<inter> Q2) ) (R, R')\<^sub>a"
   unfolding Sta_def Sta\<^sub>sS_def related_transitions_def and_rel_def
   by fast

lemma sta_s_and_rel_simp:
"Sta\<^sub>sS (P1\<odot>Q1) ((R, R')\<^sub>a) = Sta\<^sub>sS ((P1\<odot>\<lbrace>True\<rbrace>) \<inter> (\<lbrace>True\<rbrace>\<odot>Q1)) ((R, R')\<^sub>a)"
   unfolding Sta_def Sta\<^sub>sS_def related_transitions_def and_rel_def
   by fast

lemma Sta_and_dest:"Sta\<^sub>sS (P1\<odot>P2) ((R, R')\<^sub>a) = 
       Sta\<^sub>sS ({(x,y). x\<in>P1} \<inter> {(x,y). y\<in>P2}) (R, R')\<^sub>a" 
   unfolding Sta_def Sta\<^sub>sS_def related_transitions_def and_rel_def
   by fast

lemma Sta_and_dest1:"Sta\<^sub>sS (P \<inter> (P1\<odot>P2)) ((R, R')\<^sub>a) = 
                     Sta\<^sub>sS ({(x,y). x\<in>P1} \<inter> {(x,y). y\<in>P2} \<inter> P) (R, R')\<^sub>a "
   unfolding Sta_def Sta\<^sub>sS_def related_transitions_def and_rel_def
   by fast

lemma Sta_and_dest2: "(Sta\<^sub>sS ({(x,y). P1 x \<and> P2 x} \<inter> P3) ((R, R')\<^sub>a)) = 
                      (Sta\<^sub>sS (({(x,y). P1 x} \<inter>  {(x,y). P2 x}) \<inter> P3) ((R, R')\<^sub>a))"
  unfolding Sta_def Sta\<^sub>sS_def related_transitions_def and_rel_def
  by auto


lemma sta_s_int_intro:"Sta\<^sub>sS A R \<Longrightarrow> 
       Sta\<^sub>sS B R \<Longrightarrow>
       Sta\<^sub>sS (A \<inter> B) R"
  unfolding Sta\<^sub>sS_def by auto





lemma hoare_p_in_q: assumes 
  a0:"\<Gamma>1\<turnstile> \<langle>C,Normal \<sigma>n\<rangle> \<Rightarrow> Normal \<sigma>n'" and
  a1:"\<sigma>n\<in>P" and
  a2:"\<Gamma>1\<turnstile> P C Q,A "
shows "\<sigma>n' \<in>Q"
proof-
  have "\<Gamma>1,{}\<Turnstile>\<^bsub>/{}\<^esub> P C Q,A"
    using hoare_sound[OF a2] by auto
  thus ?thesis unfolding cvalid_def valid_def using a0 a1  by auto
qed

lemma hoare_not_in_s:
  assumes a0:"\<Gamma>1\<turnstile> \<langle>C,Normal \<sigma>n\<rangle> \<Rightarrow> Abrupt \<sigma>n'"  and
          a1:"\<sigma>n \<in> P" and
          a2:"\<Gamma>1 \<turnstile>P C Q,{}"           
        shows "M"
proof-
 have "\<Gamma>1,{}\<Turnstile>\<^bsub>/{}\<^esub> P C Q,{}"
    using hoare_sound[OF a2] by auto
  thus ?thesis unfolding cvalid_def valid_def using a0 a1  by auto
qed
  

definition alpha_ArincG::"(vars, vars) invs" ("\<alpha>\<^sub>A\<^sub>g")
  where
    "alpha_ArincG \<equiv> 
  {(\<sigma>,\<Sigma>). length (locals_' \<sigma>) = length (locals_' \<Sigma>) \<and>
           (\<forall>i. 
              evnt ((locals_' \<sigma>)!i) = evnt ((locals_' \<Sigma>)!i) \<and> 
              pt ((locals_' \<sigma>)!i) = pt ((locals_' \<Sigma>)!i) \<and>
              msg ((locals_' \<sigma>)!i) = msg ((locals_' \<Sigma>)!i) \<and>
              schedule ((locals_' \<sigma>)!i) = schedule ((locals_' \<Sigma>)!i) \<and>
              ret_msg ((locals_' \<sigma>)!i) = ret_msg ((locals_' \<Sigma>)!i) \<and>
              (mut (the (chans (communication_' \<sigma>) 
                (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> !i))))) \<noteq> i+1 \<longrightarrow>
                  ret_n ((locals_' \<sigma>)!i) = ret_n ((locals_' \<Sigma>)!i)) \<and>              
                  (\<forall>ch_id.                  
                    mut (the (chans (communication_' \<sigma>) ch_id)) \<noteq> i+1 \<longrightarrow> 
                        a_que_aux ((locals_' \<sigma>)!i) ch_id = a_que_aux ((locals_' \<Sigma>)!i) ch_id \<and>
                        r_que_aux ((locals_' \<sigma>)!i) ch_id = r_que_aux ((locals_' \<Sigma>)!i) ch_id)                
           ) \<and>           
           ports (communication_' \<sigma>) = ports (communication_' \<Sigma>) \<and>
           {ch. chans (communication_' \<sigma>) ch = None} = 
             {ch. chans (communication_' \<Sigma>) ch = None} \<and>
            {ch. \<exists>ch1. chans (communication_' \<sigma>) ch = Some ch1 \<and> chan_queuing ch1} = 
              {ch. \<exists>ch1. chans (communication_' \<Sigma>) ch = Some ch1 \<and> chan_queuing ch1} \<and>
           (\<forall>ch_id.             
              (mut (the (chans (communication_' \<sigma>) ch_id)) = 
                mut (the (chans (communication_' \<Sigma>) ch_id))) \<and>
              ( 
                mut (the (chans (communication_' \<Sigma>) ch_id)) = 0 \<longrightarrow>
                 data (the (chans (communication_' \<sigma>) ch_id)) =                            
                     data (the (chans (communication_' \<Sigma>) ch_id))))
            }" 

lemma Domain_\<alpha>True:"\<lbrace>True\<rbrace> = Domain \<alpha>\<^sub>A\<^sub>g" 
  unfolding alpha_ArincG_def by auto

lemma Image_\<alpha>True:"\<lbrace>True\<rbrace> = Range \<alpha>\<^sub>A\<^sub>g" 
  unfolding alpha_ArincG_def by auto
       
lemma alpha_simmetric:"(sa,sa)\<in>\<alpha>\<^sub>A\<^sub>g"    
  unfolding alpha_ArincG_def by auto

lemma channel_spec_mut_dest2:
    "channel_spec_mut B  adds rems ch_id x \<Longrightarrow>
    (chans (communication_' x) ch_id) = Some ch \<and> 
     ch_id_queuing conf ch_id \<and>  mut ch = 0 \<Longrightarrow> 
    ch_spec B  adds rems ch_id x"
unfolding channel_spec_mut_def ch_spec_def by fastforce

lemma eq_aux: 
  assumes 
  a0:"(\<sigma>,\<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g" and  
  a00:"(chans (communication_' \<sigma>) ch_id) = Some ch" and
  a02:"channel_get_mutex ch = 0" 
  shows "\<forall>i<length (locals_' \<sigma>). 
            a_que_aux ((locals_' \<sigma>)!i) ch_id = a_que_aux((locals_' \<Sigma>)!i) ch_id \<and>
            r_que_aux ((locals_' \<sigma>)!i) ch_id = r_que_aux ((locals_' \<Sigma>)!i) ch_id"
  using a00 a02 a0 unfolding channel_get_mutex_def alpha_ArincG_def  by auto
    
lemma a1:
  assumes a0:"(\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g" and 
          a1:"channel_spec_mut B adds rems ch_id \<Sigma>" and 
          a2:"state_conf \<Sigma>"
        shows "channel_spec_mut B adds rems ch_id \<sigma>"      
proof-
  have eq_len:"length (locals_' \<sigma>) = length (locals_' \<Sigma>)"  
    using a0 unfolding alpha_ArincG_def by auto 
  {fix  ch
   assume a00:"(chans (communication_' \<sigma>) ch_id) = Some ch" and 
          a01:"ch_id_queuing conf ch_id" and 
          a02:"channel_get_mutex ch = 0" 

   then have eq_mut:"(mut (the (chans (communication_' \<sigma>) ch_id)) = 
                mut (the (chans (communication_' \<Sigma>) ch_id))) \<and>
              (mut (the (chans (communication_' \<Sigma>) ch_id)) = 0 \<longrightarrow>
                 data (the (chans (communication_' \<sigma>) ch_id)) =                            
                     data (the (chans (communication_' \<Sigma>) ch_id)))"
     using a0 unfolding alpha_ArincG_def by blast
   moreover obtain chs where s20:"(chans (communication_' \<Sigma>) ch_id) = Some chs \<and> 
                                  ch_id_queuing conf ch_id \<and> mut chs = 0"
     using  a00 a01 a2 a0 a02 calculation
     unfolding alpha_ArincG_def ch_id_queuing_def state_conf_def channel_get_mutex_def by fastforce        
   have eq_data:"data (the (chans (communication_' \<sigma>) ch_id)) =                            
                     data (the (chans (communication_' \<Sigma>) ch_id))"  
     using eq_mut a00 a02 channel_get_mutex_def by auto    
   have eq_aux1:"\<forall>i<length (locals_' \<sigma>). 
            a_que_aux ((locals_' \<sigma>)!i) ch_id = a_que_aux ((locals_' \<Sigma>)!i) ch_id \<and>
            r_que_aux ((locals_' \<sigma>)!i) ch_id = r_que_aux ((locals_' \<Sigma>)!i) ch_id"
     using a00 a01 a02 eq_aux[OF a0] by auto
   then have eq_aux: "channel_sent_messages  ch_id adds (locals_' \<sigma>) = 
                        channel_sent_messages  ch_id adds  (locals_' \<Sigma>) \<and>
             channel_received_messages  ch_id rems (locals_' \<sigma>) = 
                channel_received_messages  ch_id rems (locals_' \<Sigma>)"
    using same_channel_messages[OF _ eq_len]
    unfolding  channel_sent_messages_def channel_received_messages_def
    by (simp add: eq_len)
   have "channel_get_messages ch = 
          (B ch_id + channel_sent_messages  ch_id adds (locals_' \<sigma>)) -
               channel_received_messages  ch_id  rems (locals_' \<sigma>) \<and>
         channel_received_messages  ch_id rems (locals_' \<sigma>)  \<subseteq>#
           (B ch_id + channel_sent_messages ch_id adds (locals_' \<sigma>)) \<and>
        (size (channel_get_messages ch) \<le> 
           channel_size (get_channel conf ch_id)) \<and>
         channel_messages ch_id rems [0..<length (locals_' \<sigma>)] \<subseteq># 
           channel_messages  ch_id r_que_aux (locals_' \<sigma>) \<and>
         channel_messages ch_id adds [0..<length (locals_' \<sigma>)] \<subseteq># 
           channel_messages  ch_id a_que_aux (locals_' \<sigma>)"
     using eq_aux s20  eq_data channel_spec_mut_dest2[OF a1 s20] a00  eq_aux1 
           same_channel_messages[OF _ eq_len]
     unfolding ch_spec_def channel_get_messages_def                
     using eq_len by force       
    } thus ?thesis unfolding channel_spec_mut_def channel_get_mutex_def ch_spec_def
      by fastforce 
qed
  
    
lemma rel_chans:
assumes a0:" ch \<in> channels_conf (commconf conf)" and
        a1:"\<forall>ch\<in>channels_conf (commconf conf).
             \<exists>ch_s. chans (communication_' \<Sigma>) (channel_id ch) = Some ch_s \<and> channel_queuing ch = chan_queuing ch_s" and
        a2:"{ch. \<exists>ch1. chans (communication_' \<sigma>) ch = Some ch1 \<and> chan_queuing ch1} =
          {ch. \<exists>ch1. chans (communication_' \<Sigma>) ch = Some ch1 \<and> chan_queuing ch1}" and
        a3:"{ch. chans (communication_' \<sigma>) ch = \<tau>} = {ch. chans (communication_' \<Sigma>) ch = \<tau>}" 
      shows "\<exists>ch_s. chans (communication_' \<sigma>) (channel_id ch) = Some ch_s \<and> channel_queuing ch = chan_queuing ch_s "  
  using a0 a1 a2 a3
  using option.sel by force
    

definition pre_Arinc::"(nat \<Rightarrow> Message multiset) \<Rightarrow>  (nat \<Rightarrow> nat \<Rightarrow> (msg \<times> nat) multiset) \<Rightarrow>  (nat \<Rightarrow> nat \<Rightarrow> (msg \<times> nat) multiset) \<Rightarrow> (vars, vars) invs" ("\<xi>\<^sub>A")
  where
    "pre_Arinc B adds rems \<equiv> 
       {(\<sigma>,\<Sigma>). (\<sigma>,\<Sigma>)\<in>\<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>}"    
    
definition postn_Arinc::"(vars, vars) invs" ("\<gamma>\<^sub>n\<^sub>A")
  where
    "postn_Arinc \<equiv> \<alpha>\<^sub>A\<^sub>g"    
    
definition posta_Arinc::"(vars, vars) invs" ("\<gamma>\<^sub>a\<^sub>A")
  where
    "posta_Arinc \<equiv> \<alpha>\<^sub>A\<^sub>g"    
    
 definition pre_Arinci::"(nat \<Rightarrow> Message multiset) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> (msg \<times> nat) multiset) \<Rightarrow>  (nat \<Rightarrow> nat \<Rightarrow> (msg \<times> nat) multiset) \<Rightarrow> nat \<Rightarrow> (vars, vars) invs" ("\<xi>\<^sub>A\<^sub>i")
  where
    "pre_Arinci B adds rems i \<equiv> \<xi>\<^sub>A B adds rems"    
    
definition postn_Arinci::"nat \<Rightarrow> (vars, vars) invs" ("\<gamma>\<^sub>n\<^sub>A\<^sub>i")
where
  "postn_Arinci i \<equiv> \<alpha>\<^sub>A\<^sub>g"    
    
definition posta_Arinci::"nat \<Rightarrow> (vars, vars) invs" ("\<gamma>\<^sub>a\<^sub>A\<^sub>i")
  where
    "posta_Arinci i \<equiv> \<alpha>\<^sub>A\<^sub>g"    


definition imp_program
where "imp_program B adds rems \<equiv> ParallelCom (COBEGIN SCHEME [0 \<le> i < procs conf]
                        (ArincImp.execute_service i,
                          {s. \<forall>ch_id. s\<in>Pre_QueCom_ch_mut B adds rems ch_id} \<inter> 
                            Invariant_mut B adds rems i \<inter>
                          {s. \<forall>ch_id. \<forall>ch. (chans (communication_' s) ch_id = Some ch \<longrightarrow> mut ch = 0)},
                         Rely_Send_ReceiveQ i, Guarantee_Send_Receive i,
                        {s. \<forall>ch_id. s\<in>Pre_QueCom_ch_mut B adds rems ch_id} \<inter> 
                        Post_Arinc_i_mut B adds rems i, \<lbrace> True \<rbrace>)
                       COEND)"
  
definition spec_program          
where "spec_program B adds rems \<equiv> ParallelCom (COBEGIN SCHEME [0 \<le> i < procs conf]
                        (ArincSpecQueue.execute_service i, 
                           {s. \<forall>ch_id. s\<in>Pre_QueCom_ch_mut B adds rems ch_id} \<inter> 
                               Invariant_mut B adds rems i \<inter>
                            {s. \<forall>ch_id. \<forall>ch. (chans (communication_' s) ch_id = Some ch \<longrightarrow> mut ch = 0)},
                         ArincQueuing.Rely_Send_ReceiveQ i, ArincQueuing.Guarantee_Send_Receive i,
                         {s. \<forall>ch_id. s\<in>Pre_QueCom_ch_mut B adds rems ch_id} \<inter> 
                        Post_Arinc_i_mut B adds rems i, \<lbrace> True \<rbrace>)
                       COEND)"  
  
definition sim_prog
where "sim_prog B adds rems \<equiv> (COBEGIN SCHEME [0 \<le> i < procs conf]
                        (ArincImp.execute_service i, 
                         Rely_Send_ReceiveQ i,  Guarantee_Send_Receive i, 
                         ArincSpecQueue.execute_service i, 
                         ArincQueuing.Rely_Send_ReceiveQ i, ArincQueuing.Guarantee_Send_Receive i,
                         \<xi>\<^sub>A\<^sub>i B adds rems i, \<gamma>\<^sub>n\<^sub>A\<^sub>i i, \<gamma>\<^sub>a\<^sub>A\<^sub>i i)
                       COEND)"
  
lemma eq_id:"Relation.Id = CRef.Id"  unfolding CRef.Id_def Relation.Id_def by auto
    

lemma Rn_a_x:" R\<^sub>n \<subseteq> \<alpha>\<^sub>x" unfolding alpha_xstate_def normal_relation_id_def by auto
    
lemma imp_program_list:"PCom\<^sub>c (sim_prog B adds rems) =  imp_program B adds rems"  
  unfolding PCom\<^sub>c_def imp_program_def Com\<^sub>c_def sim_prog_def ParallelCom_def
  by auto
    
lemma spec_program_list:"PCom\<^sub>s (sim_prog B adds rems) =  spec_program B adds rems"  
  unfolding PCom\<^sub>s_def spec_program_def Com\<^sub>s_def sim_prog_def ParallelCom_def
  by auto    


lemma sta_s': "Sta\<^sub>sS (\<xi>\<^sub>A\<^sub>i B adds rems i) (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+)\<^sub>\<alpha>\<^sub>A\<^sub>g"    
  unfolding Sta\<^sub>sS_def related_transitions_def pre_Arinci_def pre_Arinc_def   
  unfolding  Rely_Send_ReceiveQ_def by auto

lemma sta_s: "Sta\<^sub>s (\<xi>\<^sub>A\<^sub>i B adds rems i) (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using sta_s' by auto 

lemma sta_s_1':"
    Sta\<^sub>sS ( \<xi>\<^sub>A\<^sub>i B adds rems i \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
    \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace>)
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+)\<^sub>\<alpha>\<^sub>A\<^sub>g"
unfolding Sta\<^sub>sS_def related_transitions_def pre_Arinci_def pre_Arinc_def   and_rel_def
          alpha_ArincG_def Rely_Send_ReceiveQ_def by auto

lemma sta_s_1:"
    Sta\<^sub>s ( \<xi>\<^sub>A\<^sub>i B adds rems i \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
    \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace>)
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using sta_s_1' by auto

lemma chans_q:
  assumes a0:"(x,y) \<in> (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+"              
  shows "\<forall>x1. x = Normal x1 \<and> 
        mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 !i))))) = Suc i \<longrightarrow> 
          (\<exists>ny. y =Normal ny \<and> chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 !i))) = 
             chans (communication_' ny) (port_channel conf (communication_' ny) (pt (locals_' ny !i))))"
  using a0 
proof(induct rule: trancl_trans_induct[of _ _ "(ArincQueuing.Rely_Send_ReceiveQ i)" ])
  case 1
  then show ?case using a0 by auto
next
  case (2 x y)
  then show ?case 
   unfolding ArincQueuing.Rely_Send_ReceiveQ_def ArincQueuing.Rely_Send_Receive_def Let_def
 port_channel_def port_in_channel_def port_id_name_def port_exists_def 
   by force
next
  case (3 x y z)  
  show ?case using rely_normal_tran[OF  3(1)]  3(2)[OF 3(1)] a0  3(4)[OF 3(3)] a0    
    by metis    
qed


lemma ports_q:
  assumes a0:"(x,y) \<in> (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+"              
  shows "\<forall>x1. x = Normal x1  \<longrightarrow> (\<exists>y1. y = Normal y1 \<and> ports (communication_' x1) = ports (communication_' y1))"
  using a0 
proof(induct rule: trancl_trans_induct[of _ _ "(ArincQueuing.Rely_Send_ReceiveQ i)" ])
  case 1
  then show ?case using a0 by auto
next
  case (2 x y)
  then show ?case unfolding ArincQueuing.Rely_Send_ReceiveQ_def
   ArincQueuing.Rely_Send_Receive_def Let_def by fast
next
  case (3 x y z)  
  show ?case using rely_normal_tran[OF  3(1)]  3(2)[OF 3(1)] a0  3(4)[OF 3(3)] a0    
    by metis    
qed

lemma locals_eq:
  assumes a0:"(x,y) \<in> (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+"              
  shows "\<forall>x1. x = Normal x1 \<longrightarrow> (\<exists>y1. y = Normal y1 \<and> locals_' x1 ! i = locals_' y1 ! i)"
  using a0
proof(induct rule: trancl_trans_induct[of _ _ "(ArincQueuing.Rely_Send_ReceiveQ i)" ])
  case 1
  then show ?case using a0 by auto
next
  case (2 x y)
  then show ?case unfolding ArincQueuing.Rely_Send_ReceiveQ_def
   ArincQueuing.Rely_Send_Receive_def Let_def by fast
next
  case (3 x y z)  
  show ?case using rely_normal_tran[OF  3(1)]  3(2)[OF 3(1)] a0  3(4)[OF 3(3)] a0    
    by metis    
qed

lemma ports_eq_imp:
  assumes a0:"(Normal x,Normal y) \<in> (ArincImp.Rely_Send_ReceiveQ i)"              
  shows "ports (communication_' x) = ports (communication_' y)"
 using a0 unfolding  Rely_Send_ReceiveQ_def Rely_Send_Receive_def Sta_def   
    Let_def by fastforce

lemma locals_eq_imp:
assumes a0:"(Normal x,Normal y) \<in> (ArincImp.Rely_Send_ReceiveQ i)"              
  shows "locals_' x ! i = locals_' y ! i"
 using a0 unfolding  Rely_Send_ReceiveQ_def Rely_Send_Receive_def Sta_def   
    Let_def by fastforce

(*lemma ports_q_normal:   
  assumes a0:"(Normal x,Normal y) \<in> (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+"              
  shows "ports (communication_' x) = ports (communication_' y)"
  using ports_q[OF a0] by auto

lemma locals_q_normal:   
  assumes a0:"(Normal x,Normal y) \<in> (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+"              
  shows "locals_' x ! i = locals_' y ! i"
  using locals_eq[OF a0] by auto *)

lemma ports_q_normal:   
  assumes a0:"(Normal x, y) \<in> (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+"              
  shows "\<exists>y1. y=Normal y1 \<and> ports (communication_' x) = ports (communication_' y1)"
  using ports_q[OF a0] by auto

lemma locals_q_normal:   
  assumes a0:"(Normal x, y) \<in> (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+"              
  shows "\<exists>y1. y=Normal y1 \<and> locals_' x ! i = locals_' y1 ! i"
  using locals_eq[OF a0] by auto


lemma eq_port_channel_spec:
  assumes a0:"(Normal x, y) \<in> (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+"
  shows "\<exists>y1. y =Normal y1 \<and> port_channel conf (communication_' x) (pt (locals_' x ! i)) =  
         port_channel conf (communication_' y1) (pt (locals_' y1 ! i))"
  using ports_q_normal[OF a0] locals_q_normal[OF a0 ]
  unfolding port_channel_def port_in_channel_def port_id_name_def port_exists_def
  by auto


lemma chans_q_normal:
  assumes a0:"(Normal x, y) \<in> (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+"  and
          a1:"mut (the (chans (communication_' x) (port_channel conf (communication_' x) (pt (locals_' x !i))))) = Suc i"
  shows "\<exists>ny. y = Normal ny \<and> chans (communication_' x) (port_channel conf (communication_' x) (pt (locals_' x !i))) = 
             chans (communication_' ny) (port_channel conf (communication_' ny) (pt (locals_' ny !i)))"
  using a1 chans_q[OF a0] by auto

lemma port_opens:
  "ports (communication_' x) = ports (communication_' y) \<Longrightarrow>
   port_open (communication_' x) prt = port_open (communication_' y) prt"  
  unfolding port_open_def port_exists_def by auto

lemma Sta_port_open_Spec: "Sta \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace> ((ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+)"
  unfolding Sta_def      
  apply auto
  by (metis locals_q_normal port_opens ports_q_normal xstate.inject(1))

lemma Sta_port_open_imp: "Sta \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace> (ArincImp.Rely_Send_ReceiveQ i)"  
  unfolding Sta_def
  apply auto
  using ports_eq_imp port_opens locals_eq_imp imp_rely_normal_tran
  by metis
  
lemma ports: "(Normal x,Normal y) \<in> ArincImp.Rely_Send_ReceiveQ i \<Longrightarrow>
       ports (communication_' x) = ports (communication_' y)"
  unfolding ArincImp.Rely_Send_ReceiveQ_def ArincImp.Rely_Send_Receive_def Let_def by auto



lemma not_cond_imp_in_rel:"\<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> = 
      \<alpha>\<^sub>A\<^sub>g `` \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>"
  apply (auto simp add: alpha_ArincG_def )       
  unfolding p_queuing_def   port_exists_def
    port_channel_def port_in_channel_def port_id_name_def port_open_def
    p_source_def  port_id_in_part_def port_max_size_def 
  by auto
  

lemma Sta\<^sub>s_not_cond':"
Sta\<^sub>sS (\<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot> 
           \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"    
  using sta_in_image_sta\<^sub>s[OF sta_not_cond not_cond_imp_in_rel] by blast

lemma Sta\<^sub>s_not_cond:"
Sta\<^sub>sS (\<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot> 
           \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using Sta\<^sub>s_not_cond' by auto

lemma cond_imp_in_rel:"(-\<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) = 
      \<alpha>\<^sub>A\<^sub>g `` (-\<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)"
  apply (auto simp add: alpha_ArincG_def )       
  unfolding p_queuing_def   port_exists_def
    port_channel_def port_in_channel_def port_id_name_def port_open_def
    p_source_def  port_id_in_part_def port_max_size_def 
  by auto

lemma port_open_imp_in_rel:"\<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace> = 
      \<alpha>\<^sub>A\<^sub>g `` \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace>"
  apply (auto simp add: alpha_ArincG_def )       
  unfolding p_queuing_def   port_exists_def
    port_channel_def port_in_channel_def port_id_name_def port_open_def
    p_source_def  port_id_in_part_def port_max_size_def 
  by auto

lemma channel:
  assumes a0:"ch \<in> channels_conf (commconf conf)" and
          a1:"\<forall>ch\<in>channels_conf (commconf conf).
             \<exists>ch_s. chans (communication_' \<sigma>) (channel_id ch) = Some ch_s \<and>
                    channel_queuing ch = chan_queuing ch_s" and       
         a1':" {ch. chans (communication_' \<sigma>) ch = None} = {ch. chans (communication_' \<Sigma>) ch = None}" and
      a2:"{ch. \<exists>ch1. chans (communication_' \<sigma>) ch = Some ch1 \<and> chan_queuing ch1} =
          {ch. \<exists>ch1. chans (communication_' \<Sigma>) ch = Some ch1 \<and> chan_queuing ch1}"
    shows"\<exists>ch_s. chans (communication_' \<Sigma>) (channel_id ch) = Some ch_s \<and> channel_queuing ch = chan_queuing ch_s"
using a0 a1 a1' a2
  using option.sel by force

lemma a2_inv:" state_conf \<sigma> \<Longrightarrow> (\<sigma>,\<Sigma>)\<in> \<alpha>\<^sub>A\<^sub>g \<Longrightarrow>state_conf \<Sigma>"
  unfolding state_conf_def alpha_ArincG_def port_exists_def   
  by (auto intro: channel)
   
lemma a2:"(\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<Longrightarrow>  state_conf \<Sigma> \<Longrightarrow> state_conf \<sigma> "      
  unfolding  alpha_ArincG_def  state_conf_def port_exists_def         
  using rel_chans by auto

lemma a3:"channel_spec_mut B adds rems chid \<sigma> \<Longrightarrow> state_conf \<sigma> \<Longrightarrow> \<exists>\<Sigma>\<in> {\<Sigma>. state_conf \<Sigma> \<and> channel_spec_mut  B adds rems chid \<Sigma>}. (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g"
  unfolding alpha_ArincG_def
  by auto

lemma sta_cond_spec:"Sta (-\<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)
       ((ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+)"
 unfolding Sta_def 
     p_queuing_def   port_exists_def
    port_channel_def port_in_channel_def port_id_name_def port_open_def
    p_source_def  port_id_in_part_def port_max_size_def port_id_in_part_def
  using ports_q_normal locals_q_normal    
  apply auto 
  by (force simp add: ports_q_normal locals_q_normal)



lemma Sta\<^sub>s_cond':"
Sta\<^sub>sS ((-\<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
           (-\<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>))
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"    
  using sta_in_image_sta\<^sub>s[OF sta_cond cond_imp_in_rel] by blast

lemma Sta\<^sub>s_cond:"
Sta\<^sub>s ((-\<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
           (-\<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>))
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"   
  using Sta\<^sub>s_cond' by auto

lemma Sta\<^sub>s_port_open':"Sta\<^sub>sS (\<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot> 
           \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) 
   (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g " 
  unfolding Sta\<^sub>sS_def related_transitions_def and_rel_def
  apply auto
  using Sta_port_open_imp Sta_port_open_Spec unfolding Sta_def
  by blast+

lemma Sta\<^sub>s_port_open:"Sta\<^sub>s (\<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot> 
           \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) 
   (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g " 
  using Sta\<^sub>s_port_open' by auto

lemma sta_s_2':" Sta\<^sub>sS ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>
           \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
           \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot> 
           \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using Sta\<^sub>s_not_cond sta_s_1 unfolding pre_Arinci_def pre_Arinc_def 
  by (fastforce intro: sta_s_int_intro)

lemma sta_s_2:" Sta\<^sub>s ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>
           \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
           \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot> 
           \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using sta_s_2' by auto


lemma sta_s_3':" Sta\<^sub>sS ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>
           \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>))
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using Sta\<^sub>s_cond sta_s_1 unfolding pre_Arinci_def pre_Arinc_def 
  by (fastforce intro: sta_s_int_intro)

lemma sta_s_3:" Sta\<^sub>s ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>
           \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>))
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using sta_s_3' by auto

lemma mut_i_imp_in_rel:"(\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) = 
      \<alpha>\<^sub>A\<^sub>g `` (\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>)"
  apply (auto simp add: alpha_ArincG_def )       
  unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Let_def  
      port_get_mutex_def channel_get_mutex_def port_exists_def
    port_channel_def port_in_channel_def port_id_name_def
  by auto

lemma sta_s_por_get_mutex_suc':"Sta\<^sub>sS 
           (\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>)
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using sta_in_image_sta\<^sub>s[OF sta_mut_i mut_i_imp_in_rel] by blast

lemma sta_s_por_get_mutex_suc:"Sta\<^sub>s 
           (\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>)
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using sta_s_por_get_mutex_suc' by auto

lemma Sta_get_mutex_spec:
   "Sta \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>
               ((ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)" 
  unfolding Sta_def port_get_mutex_def Let_def channel_get_mutex_def  
  by (auto dest: chans_q_normal)

lemma  Sta_chan_spec: 
   "Sta (\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter> 
         {\<Sigma>. chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) = ch})
               ((ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)" 
  unfolding Sta_def port_get_mutex_def Let_def channel_get_mutex_def  
  by (auto dest: chans_q_normal)

lemma  Sta_chan_data_spec: 
   "Sta (\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter> 
         {\<Sigma>. data (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))))) = d})
               ((ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)" 
  unfolding Sta_def port_get_mutex_def Let_def channel_get_mutex_def  
  by (auto dest: chans_q_normal)

lemma  Sta_port_full_spec: 
   "Sta (\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter> 
         (-\<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>))
               ((ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>+)" 
  unfolding Sta_def port_get_mutex_def Let_def channel_get_mutex_def port_full_def
  channel_full_def   
  apply auto
  apply (frule chans_q_normal, frule eq_port_channel_spec, simp)
  using eq_port_channel_spec by fastforce  

lemma mut_i_chan_stable':"
Sta\<^sub>sS  ({(\<sigma>, \<Sigma>). chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))} \<inter> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) 
 (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using Sta_chan_imp Sta_chan_spec  unfolding Sta_def related_transitions_def  Sta\<^sub>sS_def and_rel_def 
  by fastforce

lemma mut_i_chan_stable:"
Sta\<^sub>s  ({(\<sigma>, \<Sigma>). chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))} \<inter> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) 
 (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using mut_i_chan_stable' by auto


lemma get_data_sta:
   "Sta (\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter> 
         {\<Sigma>. channel_get_messages ( the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))))) = d})
               ((ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)" 
  unfolding Sta_def port_get_mutex_def Let_def channel_get_mutex_def  
  by (auto dest: chans_q_normal)

lemma Sta_aux_a_spec:
   "Sta \<lbrace>a_que_aux (\<acute>locals ! i)
            (port_channel conf \<acute>communication (pt (\<acute>locals ! i))) = a\<rbrace>
               ((ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)" 
  unfolding Sta_def port_get_mutex_def Let_def channel_get_mutex_def
  using eq_port_channel_spec locals_eq by fastforce     

lemma mut_i_data_stable':"
Sta\<^sub>sS  ({(\<sigma>, \<Sigma>). data( the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) = 
                data( the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) 
 (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using Sta_chan_imp Sta_chan_spec  unfolding Sta_def related_transitions_def  Sta\<^sub>sS_def and_rel_def 
  by fastforce

lemma mut_i_data_stable:"
Sta\<^sub>s  ({(\<sigma>, \<Sigma>). data( the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) = 
                data( the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) 
 (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using mut_i_data_stable' by auto


lemma sta_locals_imp:
  "Sta \<lbrace>(\<acute>locals ! i) = l\<rbrace> (ArincImp.Rely_Send_ReceiveQ i)" 
  unfolding Sta_def ArincImp.Rely_Send_ReceiveQ_def 
           ArincImp.Rely_Send_Receive_def Let_def            
  by fastforce

lemma sta_locals_spec:
"Sta \<lbrace>(\<acute>locals ! i) = l1\<rbrace> ((ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)" 
unfolding Sta_def      
  apply clarsimp apply (frule rely_normal_tran)
  by (auto dest: locals_eq rely_normal_tran)  

lemma sta_s_locals': 
"Sta\<^sub>sS (\<lbrace>(\<acute>locals ! i) = li\<rbrace> \<odot> \<lbrace>(\<acute>locals ! i) = ls\<rbrace>) 
  (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using Sta_\<^sub>s[OF sta_locals_imp sta_locals_spec] unfolding and_rel_def by blast

lemma sta_s_locals: 
"Sta\<^sub>s (\<lbrace>(\<acute>locals ! i) = li\<rbrace> \<odot> \<lbrace>(\<acute>locals ! i) = ls\<rbrace>) 
  (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using sta_s_locals' by auto

lemma  Sta_aux_spec: 
   "Sta ({\<Sigma>. a_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) = a \<and>
             r_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) = r})
               ((ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)" 
  using sta_locals_spec eq_port_channel_spec  unfolding Sta_def  
  by fastforce

lemma  Sta_a_aux_spec: 
   "Sta ({\<Sigma>. a_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) = a})
               ((ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)" 
  using sta_locals_spec eq_port_channel_spec  unfolding Sta_def   
  by (fastforce)

lemma  Sta_r_aux_spec: 
   "Sta ({\<Sigma>. r_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) = a})
               ((ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)" 
  using sta_locals_spec eq_port_channel_spec  unfolding Sta_def   
  by fastforce
  
lemma sta_s_a_aux':"Sta\<^sub>sS 
           ({(\<sigma>, \<Sigma>). a_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                      a_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))})
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using Sta_a_aux_spec Sta_a_imp 
  unfolding Sta\<^sub>sS_def related_transitions_def Sta_def
  by force

lemma sta_s_a_aux:"Sta\<^sub>s 
           ({(\<sigma>, \<Sigma>). a_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                      a_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))})
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using sta_s_a_aux' by auto

lemma sta_s_r_aux':"Sta\<^sub>sS 
           ({(\<sigma>, \<Sigma>). r_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                      r_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))})
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using Sta_r_aux_spec Sta_r_imp 
  unfolding Sta\<^sub>sS_def related_transitions_def Sta_def
  by force

lemma sta_s_r_aux:"Sta\<^sub>s 
           ({(\<sigma>, \<Sigma>). r_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                      r_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))})
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using sta_s_r_aux' by auto

lemma sta_s_aux': "Sta\<^sub>sS 
           ({(\<sigma>, \<Sigma>). a_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                      a_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and> 
                     r_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                      r_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))})
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using sta_s_a_aux' sta_s_r_aux' unfolding Sta\<^sub>sS_def by blast

lemma sta_s_aux: "Sta\<^sub>s 
           ({(\<sigma>, \<Sigma>). a_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                      a_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and> 
                     r_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                      r_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))})
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using sta_s_a_aux sta_s_r_aux unfolding Sta\<^sub>s_def by blast

lemma sta_s_aux_data':
"Sta\<^sub>sS ({(\<sigma>, \<Sigma>). a_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                      a_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and> 
                     r_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                      r_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and> 
                data( the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) = 
                data( the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) 
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  by (blast  intro: eq_sta\<^sub>s_preS sta_s_int_intro  sta_s_aux' mut_i_data_stable')

lemma sta_s_aux_data:
"Sta\<^sub>s ({(\<sigma>, \<Sigma>). a_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                      a_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and> 
                     r_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                      r_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and> 
                data( the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) = 
                data( the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) 
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using sta_s_aux_data' by auto

lemma sta_s_4':"Sta\<^sub>sS ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>
           \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>)
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using  sta_s_3 sta_s_por_get_mutex_suc unfolding pre_Arinci_def pre_Arinc_def 
  by (fastforce intro: sta_s_int_intro)

lemma sta_s_4:"Sta\<^sub>s ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>
           \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>)
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using sta_s_4' by auto

lemma sta_s_5':"Sta\<^sub>s ({(\<sigma>, \<Sigma>). ret_n ((locals_' \<sigma>)!i) = ret_n ((locals_' \<Sigma>)!i)})
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using sta_s_locals unfolding and_rel_def
  unfolding Sta\<^sub>s_def related_transitions_def by fastforce

lemma sta_s_5S:"Sta\<^sub>sS ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>           
           \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>          
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
            {(\<sigma>, \<Sigma>). ret_n ((locals_' \<sigma>)!i) = ret_n ((locals_' \<Sigma>)!i) } \<inter>
            ({(\<sigma>, \<Sigma>). a_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                        a_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                           r_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                             r_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                           data (the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) = 
                           data (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>))
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using sta_s_5' sta_s_3 sta_s_aux_data  
  by (fastforce intro: sta_s_int_intro)

lemma sta_s_5:"Sta\<^sub>s ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>           
           \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>          
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
            {(\<sigma>, \<Sigma>). ret_n ((locals_' \<sigma>)!i) = ret_n ((locals_' \<Sigma>)!i) } \<inter>
            ({(\<sigma>, \<Sigma>). a_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                        a_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                           r_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                             r_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                           data (the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) = 
                           data (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>))
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using sta_s_5S by auto

lemma sta_s_6S:"Sta\<^sub>sS ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>           
           \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>          
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>            
            ({(\<sigma>, \<Sigma>). a_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                        a_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                           r_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                             r_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                           data (the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) = 
                           data (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>))
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using sta_s_5' sta_s_3 sta_s_aux_data  
  by (fastforce intro: sta_s_int_intro)

lemma sta_s_6:"Sta\<^sub>s ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>           
           \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>          
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>            
            ({(\<sigma>, \<Sigma>). a_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                        a_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                           r_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                             r_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                           data (the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) = 
                           data (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>))
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using sta_s_6S by auto


declare eq_related_tran[simp del]

lemma staS:"Sta\<^sub>sS (({(x, y). port_get_mutex conf (communication_' x) (pt (locals_' x ! i)) = Suc i} \<inter>
           {(x, y). port_full conf (communication_' x) (pt (locals_' x ! i))}) \<inter>
           {(x, y). port_get_mutex conf (communication_' y) (pt (locals_' y ! i)) = Suc i}) 
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using Sta_s_sta_intro[OF Sta_port_full Sta_get_mutex_spec,simplified] 
  by (auto  simp: Sta_and_dest2  )


lemma sta:"Sta\<^sub>s (({(x, y). port_get_mutex conf (communication_' x) (pt (locals_' x ! i)) = Suc i} \<inter>
           {(x, y). port_full conf (communication_' x) (pt (locals_' x ! i))}) \<inter>
           {(x, y). port_get_mutex conf (communication_' y) (pt (locals_' y ! i)) = Suc i}) 
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using staS eq_related_tran  by auto
  

  
lemma h1:"((\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
         \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
          (\<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  UNIV)) =
     (({(x, y). port_get_mutex conf (communication_' x) (pt (locals_' x ! i)) = Suc i} \<inter>
           {(x, y). port_full conf (communication_' x) (pt (locals_' x ! i))}) \<inter>
           {(x, y). port_get_mutex conf (communication_' y) (pt (locals_' y ! i)) = Suc i}) "
  unfolding and_rel_def by auto

lemma sta_6'S :"Sta\<^sub>sS 
         ((\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
         \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
          (\<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  UNIV))
(ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using h1 staS by metis

lemma sta_6' :"Sta\<^sub>s 
         ((\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
         \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
          (\<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  UNIV))
(ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using h1 sta by metis

lemma sta_port_not_full1S:"Sta\<^sub>sS (({(x, y). port_get_mutex conf (communication_' x) (pt (locals_' x ! i)) = Suc i} \<inter>
           {(x, y). \<not> port_full conf (communication_' x) (pt (locals_' x ! i))}) \<inter>
           {(x, y). port_get_mutex conf (communication_' y) (pt (locals_' y ! i)) = Suc i}) 
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using Sta_s_sta_intro[OF Sta_port_not_full Sta_get_mutex_spec]
  by (auto simp add: Sta_and_dest2 )

lemma sta_port_not_full1:"Sta\<^sub>s (({(x, y). port_get_mutex conf (communication_' x) (pt (locals_' x ! i)) = Suc i} \<inter>
           {(x, y). \<not> port_full conf (communication_' x) (pt (locals_' x ! i))}) \<inter>
           {(x, y). port_get_mutex conf (communication_' y) (pt (locals_' y ! i)) = Suc i}) 
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using eq_related_tran sta_port_not_full1S
  by auto
  
lemma h2:"((\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
         \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
          (\<lbrace>\<not>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  UNIV)) =
     (({(x, y). port_get_mutex conf (communication_' x) (pt (locals_' x ! i)) = Suc i} \<inter>
           {(x, y). \<not>port_full conf (communication_' x) (pt (locals_' x ! i))}) \<inter>
           {(x, y). port_get_mutex conf (communication_' y) (pt (locals_' y ! i)) = Suc i}) "
  unfolding and_rel_def by auto

lemma sta_port_not_fullS :"Sta\<^sub>sS 
         ((\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
         \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
          (\<lbrace>\<not>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  UNIV))
(ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using h2 sta_port_not_full1S by metis

lemma sta_port_not_full :"Sta\<^sub>s 
         ((\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
         \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
          (\<lbrace>\<not>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  UNIV))
(ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using h2 sta_port_not_full1 by metis
  

lemma eq1:"(Restr {(\<sigma>, \<Sigma>).
                        a_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                        a_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                        r_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                        r_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                        data (the (chans (communication_' \<sigma>)
                                    (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) =
                        data (the (chans (communication_' \<Sigma>)
                                    (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))}
                  \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter>
                 (\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<times>
                  \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter>
                  {(a, b). port_full conf (communication_' a) (pt (locals_' a ! i))}) \<inter>
                 Restr {(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace>) = 
        (Restr {(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
           Restr {(\<sigma>, \<Sigma>).
                  a_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                  a_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                  r_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                  r_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                  data (the (chans (communication_' \<sigma>)
                              (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) =
                  data (the (chans (communication_' \<Sigma>)
                              (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))}
            \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter>
           {(a, b). port_full conf (communication_' a) (pt (locals_' a ! i))})"
  by auto

lemma sta_6S:" Sta\<^sub>sS ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
        \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
        ({(\<sigma>, \<Sigma>).
          a_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
          a_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
          r_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
          r_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
          data (the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) =
          data (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter>
         \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
         \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
        \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  UNIV) 
(ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using   sta_s_int_intro[OF sta_s_int_intro[OF sta_s_aux_data' sta_6'S, simplified] sta_s_1' ]
  unfolding and_rel_def pre_Arinc_def pre_Arinci_def
  by (auto simp add: eq1)

lemma sta_6:" Sta\<^sub>s ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
        \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
        ({(\<sigma>, \<Sigma>).
          a_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
          a_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
          r_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
          r_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
          data (the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) =
          data (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter>
         \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
         \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
        \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  UNIV) 
(ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using  sta_6S eq_related_tran by auto

lemma sta_cond_fullS:" Sta\<^sub>sS ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>           
           \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>          
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>            
            ({(\<sigma>, \<Sigma>). a_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                        a_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                           r_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                             r_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                           data (the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) = 
                           data (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
        \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  UNIV)
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g "
  apply (subgoal_tac "{(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
       \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
       (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
           port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
           p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
           p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
           \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
       (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
           port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
           p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
           p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
           \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
       ({(\<sigma>, \<Sigma>).
         a_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
         a_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
         r_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
         r_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
         data (the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) =
         data (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter>
        \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
        \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
       (\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
        \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter>
        \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  UNIV) = 
     ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>           
           \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>          
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>            
            ({(\<sigma>, \<Sigma>). a_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                        a_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                           r_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                             r_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                           data (the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) = 
                           data (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
        \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  UNIV)")
  apply auto
  using sta_s_int_intro[OF sta_s_6S sta_6'S,of i] by auto

lemma sta_cond_full:" Sta\<^sub>s ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>           
           \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>          
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>            
            ({(\<sigma>, \<Sigma>). a_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                        a_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                           r_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                             r_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                           data (the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) = 
                           data (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
        \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  UNIV)
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g "
  using sta_cond_fullS eq_related_tran by auto
  
lemma sta_7S:" Sta\<^sub>sS ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>           
           \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>          
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>            
            ({(\<sigma>, \<Sigma>). a_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                        a_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                           r_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                             r_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                           data (the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) = 
                           data (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
        \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  UNIV \<inter>
       (\<lbrace>ret_n (\<acute>locals ! i) = Suc 0\<rbrace> \<odot>  UNIV)) 
(ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using  sta_s_int_intro[OF sta_cond_fullS  Sta_s_sta_l_intro[OF Sta_imp_ret_n]]
  unfolding and_rel_def pre_Arinc_def pre_Arinci_def
  by (auto simp add: eq1)

lemma sta_7:" Sta\<^sub>s ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>           
           \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>          
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>            
            ({(\<sigma>, \<Sigma>). a_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                        a_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                           r_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = 
                             r_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                           data (the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) = 
                           data (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
        \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  UNIV \<inter>
       (\<lbrace>ret_n (\<acute>locals ! i) = Suc 0\<rbrace> \<odot>  UNIV)) 
(ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using sta_7S eq_related_tran by auto


lemma i_lenght:"i < Sys_Config.procs conf \<Longrightarrow> state_conf a \<Longrightarrow> i<length (locals_' a)"    
  unfolding state_conf_def by auto

lemma basic_ret_0_sim:
  assumes 
   a0:"i < Sys_Config.procs conf" and
   a1:"\<xi>\<^sub>A\<^sub>1 = \<xi>\<^sub>A\<^sub>i B adds rems i" and
   a2:"\<gamma>\<^sub>n\<^sub>A\<^sub>1 = \<alpha>\<^sub>A\<^sub>g" and
   a3:"\<gamma>\<^sub>a\<^sub>A\<^sub>1 = \<gamma>\<^sub>a\<^sub>A\<^sub>i i" and
   a4:"p\<^sub>r\<^sub>e =   
       \<xi>\<^sub>A\<^sub>i B adds rems i \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace>" and
   a5:"\<sigma>' \<in> com_step (\<acute>locals ! i :== (\<acute>locals ! i)\<lparr>ret_n := 0\<rparr>) (Normal \<sigma>) ArincImp.\<Gamma>" and
   a6:"(\<sigma>, \<Sigma>)
       \<in> \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
           port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
           p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
           p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
           \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot> 
       \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
        port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
        p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
        p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
        \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>" and
    a7:"(\<sigma>, \<Sigma>) \<in> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace>" and
    a8:"(\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g" and
    a9:"length (locals_' \<sigma>) = Sys_Config.procs conf" 
  shows "\<exists>\<Sigma>'. \<Sigma>' \<in> com_step (\<acute>locals ! i :== (\<acute>locals ! i)\<lparr>ret_n := 0\<rparr>) (Normal \<Sigma>) ArincSpecQueue.\<Gamma> \<and>
             (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<and>
             (\<forall>\<sigma>n'. \<sigma>' = Normal \<sigma>n' \<longrightarrow>
                    (\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n' \<and>
                            (\<sigma>n', \<Sigma>n') \<in> \<alpha>\<^sub>A\<^sub>g \<and>
                            (Normal \<sigma>, Normal \<sigma>n') \<in> ArincImp.Guarantee_Send_Receive i \<and>
                            (Normal \<Sigma>, Normal \<Sigma>n') \<in> ArincQueuing.Guarantee_Send_Receive i)) \<and>
             (\<forall>\<sigma>n'. \<sigma>' = Abrupt \<sigma>n' \<longrightarrow>
                    (\<exists>\<Sigma>n'. \<Sigma>' = Abrupt \<Sigma>n' \<and>
                            (\<sigma>n', \<Sigma>n') \<in> \<gamma>\<^sub>a\<^sub>A\<^sub>i i \<and>
                            (Normal \<sigma>, Normal \<sigma>n') \<in> ArincImp.Guarantee_Send_Receive i \<and>
                            (Normal \<Sigma>, Normal \<Sigma>n') \<in> ArincQueuing.Guarantee_Send_Receive i))"
proof- 
  obtain \<sigma>n where \<sigma>':"\<sigma>' = Normal \<sigma>n" and \<sigma>n:"\<sigma>n = \<sigma>\<lparr>locals_' := (locals_' \<sigma>)[i := (locals_' \<sigma> ! i)\<lparr>ret_n := 0\<rparr>]\<rparr>"
    using a5 a9 a0 by auto
  let ?\<Sigma>n' = "\<Sigma>\<lparr>locals_' := (locals_' \<Sigma>)[i := (locals_' \<Sigma> ! i)\<lparr>ret_n := 0\<rparr>]\<rparr>"
  let ?\<Sigma>' = "Normal ?\<Sigma>n'"
  have a9':"length (locals_' \<Sigma>) = Sys_Config.procs conf" 
    using a9 a8 unfolding alpha_ArincG_def by auto
  then have "?\<Sigma>' \<in> com_step (\<acute>locals ! i :== (\<acute>locals ! i)\<lparr>ret_n := 0\<rparr>) (Normal \<Sigma>) ArincSpecQueue.\<Gamma>"
    using a5 a0 by auto
  moreover have  "(\<sigma>',?\<Sigma>')\<in>\<alpha>\<^sub>x" using \<sigma>' unfolding alpha_xstate_def by auto
  moreover have "(\<sigma>n, ?\<Sigma>n') \<in> \<alpha>\<^sub>A\<^sub>g" using a9 a9' \<sigma>n a8 a0 unfolding alpha_ArincG_def   
    apply simp
    apply (rule allI)
    by (case_tac "i=ia", auto) 
  moreover have "(Normal \<sigma>, Normal \<sigma>n) \<in> ArincImp.Guarantee_Send_Receive i"
    using a9 \<sigma>n a0 
    unfolding ArincImp.Guarantee_mod_chan_def ArincImp.Guarantee_Send_Receive_def 
              state_conf_def ArincImp.Guarantee_Send_Receive'_def by auto
  moreover have "(Normal \<Sigma>, Normal ?\<Sigma>n') \<in> ArincQueuing.Guarantee_Send_Receive i"
    using a9' a0 
    unfolding ArincQueuing.Guarantee_mod_chan_def ArincQueuing.Guarantee_Send_Receive'_def 
              ArincQueuing.Guarantee_Send_Receive_def state_conf_def
    by auto
  ultimately show ?thesis using \<sigma>n \<sigma>' by auto 
qed

lemma "Domain {(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} = {\<sigma>. state_conf \<sigma>}"
  unfolding alpha_ArincG_def by auto

lemma " i < Sys_Config.procs conf \<Longrightarrow>
       Domain ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter> (\<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
                  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace>)) = 
      {\<sigma>. state_conf \<sigma>} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace>"
  unfolding and_rel_def alpha_ArincG_def  by auto
   


lemma eq_domain:"i < Sys_Config.procs conf \<Longrightarrow>
     Domain ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
                  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
                  \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<and>
                   port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<and>
                   p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<and>
                   p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<and>
                   snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot> 
                  \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<and>
                   port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<and>
                   p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<and>
                   p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<and>
                   snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<inter>                   
                  ({(\<sigma>, \<Sigma>).
                    a_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                    a_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                    r_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                    r_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                    data (the (chans (communication_' \<sigma>)
                                (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) =
                    data (the (chans (communication_' \<Sigma>)
                                (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter>
                   \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
                   \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>)) = 
          {\<sigma>. state_conf \<sigma>} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter> \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<and>
                   port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<and>
                   p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<and>
                   p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<and>
                   snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<inter>
          \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>"
  unfolding and_rel_def alpha_ArincG_def
  by auto

lemma mod_mut:
  assumes   
   a1:"port_get_mutex conf c (pt (l ! i)) = 0" and
   a2:"(\<lparr>communication_' = c, locals_' = l, timer_' = t\<rparr>, b)
       \<in> \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<and>
           port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<and>
           p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<and>
           p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<and>
           snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot> 
       \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<and>
        port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<and>
        p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<and>
        p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<and>
        snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>" and
      a3:" (\<lparr>communication_' = c, locals_' = l, timer_' = t\<rparr>, b)
       \<in> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace>" and
     a4:" (\<lparr>communication_' = c, locals_' = l, timer_' = t\<rparr>, b) \<in> \<alpha>\<^sub>A\<^sub>g" and
     a5:"state_conf \<lparr>communication_' = c, locals_' = l, timer_' = t\<rparr> " 
   shows "\<lparr>communication_' = port_set_mutex conf c (pt (l ! i)) (Suc i), locals_' = l,
          timer_' = t\<rparr>
       \<in> {\<sigma>. state_conf \<sigma>} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter> \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<and>
                   port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<and>
                   p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<and>
                   p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<and>
                   snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<inter>
          \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>"
  using  a1 a2 a3 a4 a5
unfolding and_rel_def port_open_def port_id_in_part_def p_source_def p_queuing_def port_max_size_def port_set_mutex_def
    Let_def  port_set_mutex_def chan_queuing_def chan_sampling_def channel_set_mutex_def  port_exists_def
    port_channel_def port_in_channel_def port_id_name_def state_conf_def Let_def  port_set_mutex_def 
  chan_queuing_def chan_sampling_def channel_set_mutex_def  port_exists_def channel_get_mutex_def port_get_mutex_def Let_def port_set_mutex_def port_channel_def port_in_channel_def 
       port_id_name_def port_get_mutex_def port_exists_def channel_set_mutex_def
  by auto

lemma sat_await_body_mut:"i < Sys_Config.procs conf \<Longrightarrow>         
       ArincImp.\<Gamma>\<^sub>\<not>\<^sub>a
             \<turnstile> (\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = 0\<rbrace> \<inter>
                 \<lbrace>\<sigma>n. \<sigma>n \<in> Domain ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>
                                    {s. evnt (\<^bsup>s\<^esup>locals ! i) = Send_Message_Q} \<odot> 
                                    {s. evnt (\<^bsup>s\<^esup>locals ! i) = Send_Message_Q} \<inter>
                                    (- {s. port_open \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                                           port_id_in_part conf \<^bsup>s\<^esup>communication
                                            (current (schedule (\<^bsup>s\<^esup>locals ! i))) (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                                           p_source conf \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                                           p_queuing conf \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                                           \<not> snd (msg (\<^bsup>s\<^esup>locals ! i))
                                              \<le> port_max_size conf \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i))}) \<odot> 
                                    (- {s. port_open \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                                           port_id_in_part conf \<^bsup>s\<^esup>communication
                                            (current (schedule (\<^bsup>s\<^esup>locals ! i))) (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                                           p_source conf \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                                           p_queuing conf \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                                           \<not> snd (msg (\<^bsup>s\<^esup>locals ! i))
                                              \<le> port_max_size conf \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i))}))\<rbrace>)
                \<acute>communication :==\<^sub>s port_set_mutex conf \<acute>communication (pt (\<acute>locals ! i)) (Suc i)
                ({s. (Normal \<sigma>n, Normal s) \<in> ArincImp.Guarantee_Send_Receive i} \<inter>
                 Domain
                  ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
                   \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
                   (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                       port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i)))
                        (pt (\<acute>locals ! i)) \<longrightarrow>
                       p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                       p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                       \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
                   (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                       port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i)))
                        (pt (\<acute>locals ! i)) \<longrightarrow>
                       p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                       p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                       \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>                   
                   ({(\<sigma>, \<Sigma>).
                     a_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                     a_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                     r_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                     r_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                     data (the (chans (communication_' \<sigma>)
                                 (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) =
                     data (the (chans (communication_' \<Sigma>)
                                 (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter>
                    \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
                    \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>))),
                ({s. (Normal \<sigma>n, Normal s) \<in> ArincImp.Guarantee_Send_Receive i} \<inter> Domain (\<gamma>\<^sub>a\<^sub>A\<^sub>i i))"
  apply (vcg) apply auto
       apply (auto simp add: and_rel_def imp_port_set_mutex_guarantee)[1]
  using eq_domain mod_mut by auto

lemma mod_mutex_spec_guarantee:"i < Sys_Config.procs conf \<Longrightarrow>
       state_conf \<Sigma> \<Longrightarrow> 
       \<Sigma> = \<lparr>communication_' = cc, locals_' = lc, timer_' = tc, \<dots> = mc\<rparr> \<Longrightarrow>
       \<Sigma>' = \<lparr>communication_' = port_set_mutex conf cc (pt (lc ! i)) (Suc i), locals_' = lc,
           timer_' = tc, \<dots> = mc\<rparr> \<Longrightarrow>       
       port_get_mutex conf cc (pt (lc ! i)) = 0 \<Longrightarrow>
      \<Sigma> \<in> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter> \<lbrace>\<not> (port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i)))\<rbrace> \<Longrightarrow> 
      (Normal \<Sigma>, Normal \<Sigma>') \<in> ArincQueuing.Guarantee_Send_Receive i"
  unfolding state_conf_def  ArincQueuing.Guarantee_Send_Receive'_def 
         ArincQueuing.Guarantee_Send_Receive_def  port_set_mutex_def 
                port_get_mutex_def channel_get_mutex_def chan_queuing_def channel_get_messages_def
              channel_set_mutex_def ch_id_queuing_def Let_def p_queuing_def chan_sampling_def
           ArincQueuing.Guarantee_mod_chan_def  Let_def port_exists_def    
  by auto

lemma mod_mutex_post:"i < Sys_Config.procs conf \<Longrightarrow>
       state_conf \<Sigma> \<Longrightarrow> 
       \<Sigma> = \<lparr>communication_' = cc, locals_' = lc, timer_' = tc, \<dots> = mc\<rparr> \<Longrightarrow>
       \<Sigma>' = \<lparr>communication_' = port_set_mutex conf cc (pt (lc ! i)) (Suc i), locals_' = lc,
           timer_' = tc, \<dots> = mc\<rparr> \<Longrightarrow>       
       port_get_mutex conf cc (pt (lc ! i)) = 0 \<Longrightarrow>
      \<Sigma> \<in> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter> \<lbrace>\<not> (port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i)))\<rbrace> \<Longrightarrow> 
      \<Sigma>'\<in> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter> \<lbrace>\<not> (port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
         p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i)))\<rbrace> \<inter>
        \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>"
  unfolding and_rel_def port_open_def port_id_in_part_def p_source_def p_queuing_def port_max_size_def port_set_mutex_def
    Let_def  port_set_mutex_def chan_queuing_def chan_sampling_def channel_set_mutex_def  port_exists_def
    port_channel_def port_in_channel_def port_id_name_def state_conf_def Let_def  port_set_mutex_def 
  chan_queuing_def chan_sampling_def channel_set_mutex_def  port_exists_def channel_get_mutex_def port_get_mutex_def Let_def port_set_mutex_def port_channel_def port_in_channel_def 
       port_id_name_def port_get_mutex_def port_exists_def channel_set_mutex_def
  by auto  
  

lemma set_mutex_in_rel:"i < Sys_Config.procs conf \<Longrightarrow>  
       \<Sigma> = \<lparr>communication_' = cc, locals_' = lc, timer_' = tc, \<dots> = mc\<rparr>  \<Longrightarrow>
       \<Sigma>' = \<lparr>communication_' = port_set_mutex conf cc (pt (lc ! i)) (Suc i), locals_' = lc,
           timer_' = tc, \<dots> = mc\<rparr> \<Longrightarrow>
      port_get_mutex conf cc (pt (lc ! i)) = 0 \<Longrightarrow>
      \<Sigma> \<in> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter> \<lbrace>\<not> (port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i)))\<rbrace> \<Longrightarrow>
       ArincImp.\<Gamma>\<^sub>\<not>\<^sub>a
             \<turnstile> (\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = 0\<rbrace> \<inter>
                {\<sigma>. (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>
                {s. evnt (\<^bsup>s\<^esup>locals ! i) = Send_Message_Q} \<inter>
                (- {s. port_open \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                       port_id_in_part conf \<^bsup>s\<^esup>communication
                        (current (schedule (\<^bsup>s\<^esup>locals ! i))) (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                       p_source conf \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                       p_queuing conf \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                       \<not> snd (msg (\<^bsup>s\<^esup>locals ! i))
                          \<le> port_max_size conf \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i))}))
                \<acute>communication :==\<^sub>s port_set_mutex conf \<acute>communication (pt (\<acute>locals ! i)) (Suc i)
                {\<sigma>. (\<sigma>, \<Sigma>') \<in> \<alpha>\<^sub>A\<^sub>g}, \<lbrace>True\<rbrace>"
  apply (vcg) by (auto simp add: alpha_ArincG_def port_set_mutex_def channel_set_mutex_def Let_def
                   chan_queuing_def chan_sampling_def port_channel_def port_in_channel_def port_id_name_def port_exists_def 
                  channel_get_mutex_def port_get_mutex_def)

lemma sim_await_set_mut_normal:
  assumes 
  a0:"i < Sys_Config.procs conf" and
  a1:"\<sigma> = \<lparr>communication_' = c, locals_' = l, timer_' = t, \<dots> = m\<rparr>" and
  a3:"\<sigma>' = \<lparr>communication_' = ca, locals_' = la, timer_' = ta, \<dots> = ma\<rparr>" and
  a4:"\<Sigma> = \<lparr>communication_' = cc, locals_' = lc, timer_' = tc, \<dots> = mc\<rparr>" and
  a5:"\<Sigma>' = \<lparr>communication_' = port_set_mutex conf cc (pt (lc ! i)) (Suc i), locals_' = lc,
           timer_' = tc, \<dots> = mc\<rparr>" and  
   a8:"port_get_mutex conf c (pt (l ! i)) = 0" and
   a9:"ArincImp.\<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>\<acute>communication :==\<^sub>s
                         port_set_mutex conf \<acute>communication (pt (\<acute>locals ! i))
                          (Suc i),Normal \<sigma>\<rangle> \<Rightarrow> Normal \<sigma>'" and   
   a11:"state_conf \<sigma>" and
   a12:"(\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g" and
   a13:"(\<sigma>, \<Sigma>) \<in> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace>" and
   a14:"(\<sigma>, \<Sigma>)
       \<in> \<lbrace>\<not> (port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
              port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
              p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
              p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
              \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i)))\<rbrace> \<odot> 
       \<lbrace>\<not> (port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i)))\<rbrace>" and
  a15:"port_get_mutex conf cc (pt (lc ! i)) = 0" 
shows "(Normal \<Sigma>, Normal \<Sigma>') \<in> ArincQueuing.Guarantee_Send_Receive i \<and>
       (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>A\<^sub>g \<and>
       state_conf \<sigma>' \<and>
       (\<sigma>', \<Sigma>')
       \<in> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<and>
       (\<sigma>', \<Sigma>')
       \<in> \<lbrace>\<not> (port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
              port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
              p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
              p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
              \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i)))\<rbrace> \<odot> 
       \<lbrace>\<not> (port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i)))\<rbrace> \<and>       
       a_que_aux (la ! i) (port_channel conf  ca (pt (la ! i))) = a_que_aux (lc ! i)(port_channel conf (port_set_mutex conf cc (pt (lc ! i)) (Suc i))
                     (pt (lc ! i))) \<and>
       r_que_aux (la ! i) (port_channel conf  ca (pt (la ! i))) = r_que_aux (lc ! i) (port_channel conf (port_set_mutex conf cc (pt (lc ! i)) (Suc i))
                     (pt (lc ! i))) \<and>
       data (the (chans ca (port_channel conf  ca (pt (la ! i))))) =
       data (the (chans (port_set_mutex conf cc (pt (lc ! i)) (Suc i))
                   (port_channel conf (port_set_mutex conf cc (pt (lc ! i)) (Suc i))
                     (pt (lc ! i))))) \<and>
       (\<sigma>', \<Sigma>')
       \<in> \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
       \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>"
proof-
  have "(Normal \<Sigma>, Normal \<Sigma>') \<in> ArincQueuing.Guarantee_Send_Receive i"     
    using mod_mutex_spec_guarantee[OF a0 a2_inv[OF a11 a12] a4 a5 a15] 
    using a13 a14 unfolding and_rel_def
    by auto  
  moreover have rel:"(\<sigma>',\<Sigma>') \<in> \<alpha>\<^sub>A\<^sub>g" 
  proof-
    have step:"ArincImp.\<Gamma>\<^sub>\<not>\<^sub>a
             \<turnstile> (\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = 0\<rbrace> \<inter>
                {\<sigma>. (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>
                {s. evnt (\<^bsup>s\<^esup>locals ! i) = Send_Message_Q} \<inter>
                (- {s. port_open \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                       port_id_in_part conf \<^bsup>s\<^esup>communication
                        (current (schedule (\<^bsup>s\<^esup>locals ! i))) (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                       p_source conf \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                       p_queuing conf \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                       \<not> snd (msg (\<^bsup>s\<^esup>locals ! i))
                          \<le> port_max_size conf \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i))}))
                \<acute>communication :==\<^sub>s port_set_mutex conf \<acute>communication (pt (\<acute>locals ! i)) (Suc i)
                {\<sigma>. (\<sigma>, \<Sigma>') \<in> \<alpha>\<^sub>A\<^sub>g}, \<lbrace>True\<rbrace>" 
      using set_mutex_in_rel[OF a0 a4 a5 a15] a13 a14 unfolding and_rel_def by auto
    have "\<sigma>\<in>{\<sigma>. (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>
                \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = 0\<rbrace> \<inter>
                {s. evnt (\<^bsup>s\<^esup>locals ! i) = Send_Message_Q} \<inter>
                (- {s. port_open \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                       port_id_in_part conf \<^bsup>s\<^esup>communication
                        (current (schedule (\<^bsup>s\<^esup>locals ! i))) (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                       p_source conf \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                       p_queuing conf \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                       \<not> snd (msg (\<^bsup>s\<^esup>locals ! i))
                          \<le> port_max_size conf \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i))})"
      using a13 a14 a8 a1 a11 a12 unfolding and_rel_def by auto    
    then show ?thesis using hoare_p_in_q[OF a9 _ step]  by auto
  qed
  moreover have h1:"\<sigma> \<in> \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = 0\<rbrace> \<inter>
         \<lbrace>\<sigma>. \<sigma> \<in> Domain ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>
                                {s. evnt (\<^bsup>s\<^esup>locals ! i) = Send_Message_Q} \<odot> 
                                {s. evnt (\<^bsup>s\<^esup>locals ! i) = Send_Message_Q} \<inter>
                                (- {s. port_open \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                                       port_id_in_part conf \<^bsup>s\<^esup>communication (current (schedule (\<^bsup>s\<^esup>locals ! i)))
                                        (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                                       p_source conf \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                                       p_queuing conf \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                                       \<not> snd (msg (\<^bsup>s\<^esup>locals ! i))
                                          \<le> port_max_size conf \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i))}) \<odot> 
                                (- {s. port_open \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                                       port_id_in_part conf \<^bsup>s\<^esup>communication (current (schedule (\<^bsup>s\<^esup>locals ! i)))
                                        (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                                       p_source conf \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                                       p_queuing conf \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i)) \<longrightarrow>
                                       \<not> snd (msg (\<^bsup>s\<^esup>locals ! i))
                                          \<le> port_max_size conf \<^bsup>s\<^esup>communication (pt (\<^bsup>s\<^esup>locals ! i))}))\<rbrace>"
    using  a12 a13 a14 a11 a8 a1 a0 unfolding and_rel_def alpha_ArincG_def by auto  
  then have "\<sigma>' \<in> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace>  \<inter>
                   (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                       port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i)))
                        (pt (\<acute>locals ! i)) \<longrightarrow>
                       p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                       p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                       \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
                   \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter> {\<sigma>.  state_conf \<sigma>}"
    using  hoare_p_in_q[OF a9 h1 sat_await_body_mut[OF a0]] a0 
    unfolding and_rel_def alpha_ArincG_def by auto
  moreover have "a_que_aux (la ! i) (port_channel conf  ca (pt (la ! i))) = 
                 a_que_aux (lc ! i)(port_channel conf (port_set_mutex conf cc (pt (lc ! i)) (Suc i))
                     (pt (lc ! i))) \<and>
       r_que_aux (la ! i) (port_channel conf  ca (pt (la ! i))) = 
       r_que_aux (lc ! i) (port_channel conf (port_set_mutex conf cc (pt (lc ! i)) (Suc i)) (pt (lc ! i))) \<and>
       data (the (chans ca (port_channel conf  ca (pt (la ! i))))) =
       data (the (chans (port_set_mutex conf cc (pt (lc ! i)) (Suc i))
                   (port_channel conf (port_set_mutex conf cc (pt (lc ! i)) (Suc i))
                     (pt (lc ! i)))))" 
  proof-
    have "a_que_aux (l ! i) (port_channel conf  c (pt (l ! i))) = 
            a_que_aux (la ! i) (port_channel conf ca (pt (la ! i))) \<and>
       r_que_aux (l ! i) (port_channel conf  c (pt (l ! i))) = 
            r_que_aux (la ! i) (port_channel conf ca (pt (la ! i))) \<and>
       data (the (chans c (port_channel conf  c (pt (l ! i))))) =
       data (the (chans ca (port_channel conf ca (pt (la ! i)))))"
    proof-
      obtain a r d r_n where a:"\<sigma> \<in> \<lbrace>a_que_aux (\<acute>locals ! i) (port_channel conf  \<acute>communication (pt (\<acute>locals ! i))) = a \<and> 
                 r_que_aux (\<acute>locals ! i) (port_channel conf  \<acute>communication (pt (\<acute>locals ! i))) = r \<and> 
                 data (the (chans \<acute>communication (port_channel conf  \<acute>communication (pt (\<acute>locals ! i))))) = d \<and>
                 ret_n (\<acute>locals ! i) = r_n \<rbrace>"
        by auto
      have i:"ArincImp.\<Gamma>\<^sub>\<not>\<^sub>a
             \<turnstile> (\<lbrace>a_que_aux (\<acute>locals ! i) (port_channel conf  \<acute>communication (pt (\<acute>locals ! i))) = a \<and> 
                 r_que_aux (\<acute>locals ! i) (port_channel conf  \<acute>communication (pt (\<acute>locals ! i))) = r \<and> 
                 data (the (chans \<acute>communication (port_channel conf  \<acute>communication (pt (\<acute>locals ! i))))) = d \<and>
                 ret_n (\<acute>locals ! i) = r_n\<rbrace>)
                \<acute>communication :==\<^sub>s port_set_mutex conf \<acute>communication (pt (\<acute>locals ! i)) (Suc i)
                \<lbrace>a_que_aux (\<acute>locals ! i) (port_channel conf  \<acute>communication (pt (\<acute>locals ! i))) = a \<and> 
                 r_que_aux (\<acute>locals ! i) (port_channel conf  \<acute>communication (pt (\<acute>locals ! i))) = r \<and> 
                 data (the (chans \<acute>communication (port_channel conf  \<acute>communication (pt (\<acute>locals ! i))))) = d \<and> 
                 ret_n (\<acute>locals ! i) = r_n\<rbrace>, \<lbrace>True\<rbrace>"
        apply vcg unfolding port_set_mutex_def Let_def channel_set_mutex_def 
        port_channel_def port_in_channel_def port_id_name_def port_exists_def
        by auto          
      then show ?thesis using hoare_p_in_q[OF a9 a i] using a a1 a3 by auto
    qed
    moreover have "
             ret_n (l ! i) = ret_n (lc ! i) \<and>
             a_que_aux (l ! i) (port_channel conf  c (pt (l ! i))) = 
            a_que_aux (lc ! i) (port_channel conf cc (pt (lc ! i))) \<and>
       r_que_aux (l ! i) (port_channel conf  c (pt (l ! i))) = 
            r_que_aux (lc ! i) (port_channel conf cc (pt (lc ! i))) \<and>
       data (the (chans c (port_channel conf  c (pt (l ! i))))) =
       data (the (chans cc (port_channel conf cc (pt (lc ! i)))))"
      using a12 a15 a8 a1 a4 unfolding alpha_ArincG_def port_get_mutex_def channel_get_mutex_def
         port_channel_def port_in_channel_def port_id_name_def port_exists_def
      by auto     
    moreover have "              
            a_que_aux (lc ! i) (port_channel conf cc (pt (lc ! i))) = 
                a_que_aux (lc ! i)(port_channel conf (port_set_mutex conf cc (pt (lc ! i)) (Suc i))
                     (pt (lc ! i))) \<and>
              r_que_aux (lc ! i) (port_channel conf cc (pt (lc ! i))) = 
                r_que_aux (lc ! i) (port_channel conf (port_set_mutex conf cc (pt (lc ! i)) (Suc i)) (pt (lc ! i))) \<and>
              data (the (chans cc (port_channel conf cc (pt (lc ! i))))) = 
               data (the (chans (port_set_mutex conf cc (pt (lc ! i)) (Suc i))
                   (port_channel conf (port_set_mutex conf cc (pt (lc ! i)) (Suc i))
                     (pt (lc ! i)))))"
     unfolding alpha_ArincG_def port_get_mutex_def channel_get_mutex_def
         port_channel_def port_in_channel_def port_id_name_def port_exists_def port_set_mutex_def
         channel_set_mutex_def Let_def
     by auto
   ultimately show ?thesis by auto
  qed
  
  ultimately show ?thesis using mod_mutex_post[OF a0 a2_inv[OF a11 a12] a4 a5 a15] a13 a14 a11
    unfolding and_rel_def by auto    
qed

lemma no_abrupt:"ArincImp.\<Gamma>\<^sub>\<not>\<^sub>a
          \<turnstile> \<lbrace>P\<rbrace> \<acute>communication :==\<^sub>s port_set_mutex conf \<acute>communication (pt (\<acute>locals ! i)) (Suc i) \<lbrace>True\<rbrace>,{}"
  by vcg


lemma if_b1_alpha:
  assumes a0':"i< Sys_Config.procs conf" and 
          a0'': "length (locals_' \<sigma>) = Sys_Config.procs conf" and 
         a0:"(\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g" and
         a1:"state_conf \<sigma>" and
         a2:"(\<sigma>, \<Sigma>) \<in> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace>" and
         a3:"a_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
             a_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))" and
         a4:"r_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
           r_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))" and
         a5:"data (the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) =
           data (the (chans (communication_' \<Sigma>)
                       (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))" and
         a6:"(\<sigma>, \<Sigma>) \<in> \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>" and
         a7:"(\<sigma>, \<Sigma>) \<in> \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  UNIV" 
       shows "(\<sigma>\<lparr>locals_' := (locals_' \<sigma>)[i := (locals_' \<sigma> ! i)\<lparr>ret_n := Suc 0\<rparr>]\<rparr>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g"
proof- 
  show ?thesis using a0' a0'' a0 a6   
    apply (simp add: alpha_ArincG_def )
    apply (rule allI)
    apply (case_tac "i=ia") by  (auto simp add: and_rel_def port_get_mutex_def Let_def channel_get_mutex_def)
qed


lemma h:"i < Sys_Config.procs conf \<Longrightarrow>   
    \<forall>\<sigma>n\<in>Domain ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
                 \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
                 (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                     port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
                     p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                     p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                     \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
                 (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                     port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
                     p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                     p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                     \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
                 ({(\<sigma>, \<Sigma>).
                   a_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                   a_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                   r_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                   r_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                   data (the (chans (communication_' \<sigma>)
                               (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) =
                   data (the (chans (communication_' \<Sigma>)
                               (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter>
                  \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
                  \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
                 \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  UNIV \<inter>
                 \<lbrace>ret_n (\<acute>locals ! i) = Suc 0\<rbrace> \<odot>  UNIV).
       \<forall>\<sigma>n'. Normal \<sigma>n'
             \<in> com_step (\<acute>communication :== port_set_mutex conf \<acute>communication (pt (\<acute>locals ! i)) 0) (Normal \<sigma>n)
                 ArincImp.\<Gamma> \<longrightarrow>
             (Normal \<sigma>n, Normal \<sigma>n') \<in> ArincImp.Guarantee_Send_Receive i"
  unfolding ArincImp.Guarantee_Send_Receive_def Let_def Guarantee_mod_chan_def Guarantee_Send_Receive'_def
port_set_mutex_def channel_set_mutex_def state_conf_def chan_queuing_def chan_sampling_def port_exists_def
port_channel_def port_in_channel_def port_id_name_def and_rel_def port_open_def port_id_in_part_def
port_id_name_def current_def  p_queuing_def ch_id_queuing_def port_get_mutex_def channel_get_mutex_def
channel_get_messages_def
  by auto

lemma sim_send1:
"i < Sys_Config.procs conf \<Longrightarrow> 
  \<xi> = {(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter> (\<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
                  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace>) \<inter>
                  ((- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
                  (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)) \<inter>
                  ({(\<sigma>, \<Sigma>).
                    a_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                    a_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                    r_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                    r_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                    data (the (chans (communication_' \<sigma>)
                                (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) =
                    data (the (chans (communication_' \<Sigma>)
                                (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter>
                   (\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
                   \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>)) \<inter>
                  (\<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  UNIV) \<Longrightarrow>      
    (ArincImp.\<Gamma>,(\<acute>locals :== \<acute>locals[i:=((\<acute>locals!i)\<lparr>ret_n := 1\<rparr>)];;
       \<acute>communication :==\<^sub>E\<^sub>V (port_set_mutex conf \<acute>communication (pt ((\<acute>locals)!i)) 0)),ArincImp.Rely_Send_ReceiveQ i,ArincImp.Guarantee_Send_Receive i)
    \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>A\<^sub>g\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<alpha>\<^sub>A\<^sub>g\<^sub>;\<^sub>\<alpha>\<^sub>A\<^sub>g\<^sub>)
    (ArincSpecQueue.\<Gamma>,Await UNIV
                        (IF\<^sub>s port_full conf \<acute>communication (pt (\<acute>locals ! i))
                         THEN \<acute>locals ! i :==\<^sub>s (\<acute>locals ! i)\<lparr>ret_n := Suc 0\<rparr>;;\<^sub>s
                           \<acute>communication :==\<^sub>s port_set_mutex conf \<acute>communication (pt (\<acute>locals ! i)) 0
                         ELSE \<acute>communication :==\<^sub>s
                              port_insert_message conf \<acute>communication (pt (\<acute>locals ! i)) (msg (\<acute>locals ! i)) 0;;\<^sub>s
                           \<acute>locals ! i :==\<^sub>s (\<acute>locals ! i)
                           \<lparr>a_que_aux :=
                              set_que_aux conf \<acute>communication (pt (\<acute>locals ! i)) (a_que_aux (\<acute>locals ! i))
                               (add_mset (msg (\<acute>locals ! i))
                                 (get_que_aux conf \<acute>communication (pt (\<acute>locals ! i))
                                   (a_que_aux (\<acute>locals ! i))))\<rparr>;;\<^sub>s
                           \<acute>communication :==\<^sub>s port_set_mutex conf \<acute>communication (pt (\<acute>locals ! i)) 0;;\<^sub>s
                           \<acute>locals ! i :==\<^sub>s (\<acute>locals ! i)\<lparr>ret_n := Suc 0\<rparr>
                         FI)
                        (Some E\<^sub>V), ArincQueuing.Rely_Send_ReceiveQ i,ArincQueuing.Guarantee_Send_Receive i)"
  apply (rule imp_seq_Basic_Spec_sim[where \<xi>\<^sub>1 = "\<xi> \<inter> (\<lbrace>ret_n (\<acute>locals ! i) = Suc 0\<rbrace> \<odot>  UNIV)"  ])
            apply auto[2] 
          apply (fastforce intro: sta_cond_full) apply (fastforce intro: sta_7)
         apply (auto simp add:  imp_guarante_ref reflexive_Guarantee_Send 
                 Rely_Send_ReceiveQ_def ArincQueuing.Rely_Send_ReceiveQ_def alpha_xstate_def alpha_xstate'_def)[3]   
   apply auto   
    apply (simp add: alpha_ArincG_def state_conf_def and_rel_def port_get_mutex_def Let_def channel_get_mutex_def)
    apply (rule allI)
    apply (case_tac "i=ia", auto)   
   apply (auto simp add: state_conf_def and_rel_def)[9]
   apply (simp add: Guarantee_Send_Receive_def 
                         Guarantee_Send_Receive'_def state_conf_def 
                         Guarantee_mod_chan_def)
  apply (rule mod_state_Await_Spec_Sim[where F="{}"])
                 apply auto[3]
              apply (fastforce intro: sta_7)
             apply (fastforce intro: stable_related)
            apply (fastforce intro: stable_related)
           apply (simp add: imp_guarante_ref)
  apply (auto simp add: ArincImp.Rely_Send_ReceiveQ_def  ArincQueuing.Rely_Send_ReceiveQ_def alpha_xstate'_def)[4]
  apply (auto simp add:   ArincImp.Guarantee_Send_Receive_def Let_def Guarantee_mod_chan_def Guarantee_Send_Receive'_def
port_set_mutex_def channel_set_mutex_def state_conf_def chan_queuing_def chan_sampling_def port_exists_def
port_channel_def port_in_channel_def port_id_name_def and_rel_def port_open_def port_id_in_part_def
 current_def  p_queuing_def ch_id_queuing_def port_get_mutex_def channel_get_mutex_def
 channel_get_messages_def)[1]
     apply auto
  apply vcg
     apply (drule a2_inv, auto)  
  apply (auto simp add:  alpha_ArincG_def 
 ArincQueuing.Guarantee_Send_Receive_def 
  ArincQueuing.Guarantee_Send_Receive'_def  Let_def 
  ArincQueuing.Guarantee_mod_chan_def port_set_mutex_def channel_set_mutex_def state_conf_def chan_queuing_def chan_sampling_def port_exists_def
port_channel_def port_in_channel_def port_id_name_def and_rel_def port_open_def port_id_in_part_def
 current_def  p_queuing_def ch_id_queuing_def port_get_mutex_def channel_get_mutex_def
 channel_get_messages_def   port_name_in_channel_def)[1]    
  apply (simp add: alpha_ArincG_def )
  apply (rule conjI, rule allI)  
  apply (case_tac "i=ia") 
      apply (auto simp add: and_rel_def port_open_def port_id_in_part_def p_source_def 
          p_queuing_def port_max_size_def port_set_mutex_def           
          port_channel_def port_in_channel_def port_id_name_def state_conf_def Let_def   
         chan_queuing_def chan_sampling_def channel_set_mutex_def  port_exists_def 
         channel_get_mutex_def port_get_mutex_def port_name_in_channel_def)[3]
     unfolding and_rel_def port_full_def channel_full_def Let_def channel_get_bufsize_def channel_get_messages_def
alpha_ArincG_def port_channel_def port_in_channel_def port_id_name_def port_exists_def
  by auto


lemma sta_cond_not_fullS:" Sta\<^sub>sS  ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
        (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
        (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
        ({(\<sigma>, \<Sigma>).
          a_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
          a_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
          r_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
          r_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
          data (the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) =
          data (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter>
         \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
         \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
        - \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  \<lbrace>True\<rbrace>)
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g "     
  apply (rule eq_sta\<^sub>s_preS[OF sta_s_int_intro[OF sta_s_6S sta_port_not_fullS,of i]])
  unfolding and_rel_def
  by auto

lemma sta_cond_not_full:" Sta\<^sub>s  ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
        (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
        (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
        ({(\<sigma>, \<Sigma>).
          a_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
          a_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
          r_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
          r_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
          data (the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) =
          data (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter>
         \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
         \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
        - \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  \<lbrace>True\<rbrace>)
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g "   
  using eq_related_tran sta_cond_not_fullS  by auto
 

lemma Sta_channel_eq_data:"
   Sta (\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter>
            \<lbrace>channel_get_messages (the (chans \<acute>communication 
            (port_channel conf \<acute>communication (pt (\<acute>locals ! i))))) =
                    d + {#msg (\<acute>locals ! i)#}\<rbrace>)
       (ArincImp.Rely_Send_ReceiveQ i)"
unfolding Sta_def
     p_queuing_def   port_exists_def port_get_mutex_def
    port_channel_def port_in_channel_def port_id_name_def port_open_def
    p_source_def  port_id_in_part_def port_max_size_def port_id_in_part_def
 channel_get_messages_def port_full_def channel_full_def Let_def channel_get_mutex_def
channel_get_messages_def channel_get_bufsize_def Rely_Send_ReceiveQ_def Rely_Send_Receive_def
  by auto


lemma Sta_aux_a_imp:"
   Sta (\<lbrace>a_que_aux (\<acute>locals ! i)
            (port_channel conf  \<acute>communication (pt (\<acute>locals ! i))) =
           a + {#msg (\<acute>locals ! i)#}\<rbrace>)
       (ArincImp.Rely_Send_ReceiveQ i)"
unfolding Sta_def
     p_queuing_def   port_exists_def port_get_mutex_def
    port_channel_def port_in_channel_def port_id_name_def port_open_def
    p_source_def  port_id_in_part_def port_max_size_def port_id_in_part_def
 channel_get_messages_def port_full_def channel_full_def Let_def channel_get_mutex_def
channel_get_messages_def channel_get_bufsize_def Rely_Send_ReceiveQ_def Rely_Send_Receive_def
  by auto

lemma port_open_queuing_some_chan_queuing:
  assumes 
   a0:"state_conf s" and
   a1:"port_open (communication_' s) p_id" and
   a2:"p_queuing conf (communication_' s) p_id" 
 shows 
"\<exists>chan. chans (communication_' s) (port_channel conf (communication_' s) p_id) = Some chan \<and> 
  chan_queuing chan"
  using p_queuing_chan_queuing[OF a0 a1 a2] port_unique_channel[OF a0 a1] by blast

lemma port_open_queuing_some_chan:
  assumes 
   a0:"state_conf s" and
   a1:"port_open (communication_' s) p_id"
 shows 
"\<exists>chan. chans (communication_' s) (port_channel conf (communication_' s) p_id) = Some chan "
  using p_chan[OF a0 a1] port_unique_channel[OF a0 a1] by blast






lemma port_insert_mutex:
  "state_conf s \<Longrightarrow>
   port_open (communication_' s) p_id \<Longrightarrow>   
   port_get_mutex conf (port_insert_message conf (communication_' s) p_id  m t) p_id =
   port_get_mutex conf (communication_' s) p_id"
proof -
  assume a0: "state_conf s" and
         a1: " port_open (communication_' s) p_id"                   
  then have "\<exists>!ch_id. port_in_channel conf (communication_' s) p_id ch_id \<and> 
     port_channel conf (communication_' s) p_id = ch_id"
    using port_unique_channel by auto       
  then show ?thesis      
    unfolding port_get_messages_def  
           Let_def   port_insert_message_def 
           port_exists_def  port_id_name_def port_get_mutex_def  channel_get_mutex_def 
           channel_insert_message_def channel_set_messages_def port_channel_def port_in_channel_def port_id_name_def
    apply auto
    by (case_tac " data (the (chans (communication_' s)
                          (The (port_name_in_channel conf
                                 (THE p_n. (\<exists>p. ports (communication_' s) p_n = Some p) \<and>
                                           portid (the (ports (communication_' s) p_n)) = Some p_id)))))", auto)    
qed

lemma insert_message_eq_type:
     assumes 
          a0:" state_conf \<sigma>" and
          a1:"port_open (communication_' \<sigma>) p_id" 
        shows
       "{ch. \<exists>ch1. chans (port_insert_message conf (communication_' \<sigma>) p_id m t) ch = Some ch1 \<and>
               chan_queuing ch1} = 
       {ch. \<exists>ch1. chans ((communication_' \<sigma>) ) ch = Some ch1 \<and>
               chan_queuing ch1}"
  using a0 a1 port_open_queuing_some_chan[OF a0 a1]
  apply auto
  apply (case_tac "x = port_channel conf (communication_' \<sigma>) p_id", auto simp add: port_insert_message_def  chan_queuing_def 
   chan_sampling_def channel_insert_message_def, case_tac "data chan"; auto simp add: channel_set_messages_def)
  by (auto simp add: port_insert_message_def  chan_queuing_def 
   chan_sampling_def channel_insert_message_def, case_tac "data chan"; auto simp add: channel_set_messages_def)

  
lemma insert_message_eq_mut:
 assumes 
      a0:" state_conf \<sigma>" and
      a1:"port_open (communication_' \<sigma>) p_id" 
    shows
       "mut (the (chans (port_insert_message conf (communication_' \<sigma>) p_id m t) ch_id)) =
        mut (the (chans (communication_' \<sigma>) ch_id))"
  using a0 a1 port_open_queuing_some_chan[OF a0 a1]
  apply auto
  by (case_tac "ch_id = port_channel conf (communication_' \<sigma>) p_id", auto simp add: port_insert_message_def  chan_queuing_def 
   chan_sampling_def channel_insert_message_def, case_tac "data chan", auto simp add: channel_set_messages_def)

lemma insert_message_eq_data_other_channel:
 assumes 
      a0:" state_conf \<sigma>" and
      a1:"port_open (communication_' \<sigma>) p_id" and
      a2:"ch_id \<noteq> port_channel conf  (communication_' \<sigma>) p_id"
    shows
       "data (the (chans (port_insert_message conf (communication_' \<sigma>) p_id m t) ch_id)) =
        data (the (chans (communication_' \<sigma>) ch_id))"
  using a0 a1 a2 port_open_queuing_some_chan[OF a0 a1]  
  by (auto simp add: port_insert_message_def  chan_queuing_def 
   chan_sampling_def channel_insert_message_def channel_set_messages_def)
  
lemma insert_message_rel:
  assumes a0:"i < Sys_Config.procs conf" and
          a1:"(\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g" and
          a2:" state_conf \<sigma>" and
          a3:"port_open (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))" and
          a3':"port_open (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))" and                    
          a7:"port_get_mutex conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i)) = Suc i"  
  shows "(\<sigma>\<lparr>communication_' := port_insert_message conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i)) (msg (locals_' \<sigma> ! i)) 0\<rparr>, \<Sigma>)
           \<in> \<alpha>\<^sub>A\<^sub>g"
  using a0 a1 a2 a3 a3' a7
  unfolding alpha_ArincG_def
  apply simp
apply (frule  port_insert_mutex; simp add: port_get_mutex_def Let_def channel_get_mutex_def)  
  apply (rule conjI)
  apply (rule allI)                       
   apply (case_tac "i=ia";  auto simp add: channel_set_messages_def port_insert_message_def channel_insert_message_def
 Let_def port_exists_def port_channel_def port_in_channel_def port_id_name_def   
 channel_get_messages_def)
  apply (rule conjI)
   apply (auto simp add: port_get_mutex_def channel_get_mutex_def port_insert_message_def Let_def)[1]
  apply (rule conjI)
  apply(insert port_open_queuing_some_chan[OF  a2_inv[OF a2 a1]   a3'])
   apply (auto simp add: channel_set_messages_def port_insert_message_def channel_insert_message_def
 Let_def port_exists_def port_channel_def port_in_channel_def port_id_name_def   
 channel_get_messages_def )[1]
  apply (auto simp: insert_message_eq_type insert_message_eq_mut)
  by (case_tac "ch_id = (port_channel conf (communication_' \<sigma>) (pt (locals_' \<Sigma> ! i)))", 
    auto dest: insert_message_eq_data_other_channel)

lemma port_open_insert_queuing:
" port_open (communication_' s) p_id \<Longrightarrow>     
   port_open (communication_' (s\<lparr>communication_' := (port_insert_message conf (communication_' s) p_id  m t)\<rparr>)) p_id"
proof-
assume 
       a1: "port_open (communication_' s) p_id"   
  have "ports (communication_' s) = ports (communication_' (s\<lparr>communication_' := (port_insert_message conf (communication_' s) p_id  m t)\<rparr>))"
    unfolding  port_in_channel_def 
           Let_def  port_channel_def port_insert_message_def 
           port_exists_def  port_id_name_def  port_open_def  port_exists_def 
    by auto
  thus ?thesis 
    using a1
    unfolding port_get_messages_def port_in_channel_def 
           Let_def  port_channel_def port_insert_message_def 
           port_exists_def  port_id_name_def  port_open_def  port_exists_def 
    by auto
qed


lemma guarantee_insert_channel:"
  i < procs conf \<Longrightarrow>
  state_conf \<sigma> \<Longrightarrow>
  evnt (locals_' \<sigma> ! i) = Send_Message_Q \<Longrightarrow>
  port_get_mutex conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i)) = Suc i \<Longrightarrow>  
  p_queuing conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i)) \<Longrightarrow>
  port_open (communication_' \<sigma>) (pt (locals_' \<sigma> ! i)) \<Longrightarrow>
    (Normal \<sigma>,
     Normal
      (\<sigma>\<lparr>communication_' :=
           port_insert_message conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))
            (msg (locals_' \<sigma> ! i)) 0\<rparr>))
    \<in> ArincImp.Guarantee_Send_Receive i"
 unfolding Guarantee_Send_Receive_def    Guarantee_Send_Receive'_def
             port_get_mutex_def channel_get_mutex_def set_que_aux_def get_que_aux_def channel_set_messages_def 
          channel_insert_message_def Let_def port_insert_message_def channel_set_mutex_def 
          port_set_mutex_def state_conf_def  chan_queuing_def chan_sampling_def
          channel_get_messages_def port_full_def channel_full_def
             channel_get_bufsize_def  Guarantee_mod_chan_def  
             p_queuing_def   ch_id_queuing_def  port_exists_def  
        apply (case_tac "data (the (chans (communication_' \<sigma>)
             (port_channel conf  (communication_'  \<sigma>) (pt (locals_'  \<sigma> ! i)))))")   
       unfolding port_channel_def port_in_channel_def  port_id_name_def port_exists_def
       by auto

lemma sim2_seq1_post:"i < Sys_Config.procs conf \<Longrightarrow>  
    (\<sigma>, \<Sigma>) \<in> {(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>
        \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
        (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i)))
             (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i))
               \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
        (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i)))
             (pt (\<acute>locals ! i)) \<longrightarrow>
            p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
            \<not> snd (msg (\<acute>locals ! i))
               \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
        ({(\<sigma>, \<Sigma>).
          a_que_aux (locals_' \<sigma> ! i)
           (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
          a_que_aux (locals_' \<Sigma> ! i)
           (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
          r_que_aux (locals_' \<sigma> ! i)
           (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
          r_que_aux (locals_' \<Sigma> ! i)
           (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
          data (the (chans (communication_' \<sigma>)
                      (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) =
          data (the (chans (communication_' \<Sigma>)
                      (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter>
         \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
         \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
        - \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  \<lbrace>True\<rbrace> \<and>
              \<sigma>' \<in> com_step (\<acute>communication :== port_insert_message conf \<acute>communication (pt (\<acute>locals ! i)) (msg (\<acute>locals ! i)) 0)
                     (Normal \<sigma>) ArincImp.\<Gamma> \<longrightarrow>
              (\<exists>\<sigma>n'. \<sigma>' = Normal \<sigma>n' \<and>
                    (\<sigma>n', \<Sigma>)
              \<in> {(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>
                 \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
                 \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
                 \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot> 
                 (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                     port_id_in_part conf \<acute>communication
                      (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
                     p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                     p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                     \<not> snd (msg (\<acute>locals ! i))
                        \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
                 ({(\<sigma>, \<Sigma>).
                   a_que_aux (locals_' \<sigma> ! i)
                    (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                   a_que_aux (locals_' \<Sigma> ! i)
                    (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                   r_que_aux (locals_' \<sigma> ! i)
                    (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                   r_que_aux (locals_' \<Sigma> ! i)
                    (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))} \<inter>
                  {(\<sigma>, \<Sigma>).
                   \<exists>d. channel_get_messages
                        (the (chans (communication_' \<sigma>)
                               (port_channel conf (communication_' \<sigma>)
                                 (pt (locals_' \<sigma> ! i))))) =
                       d + {#msg (locals_' \<sigma> ! i)#} \<and>
                       channel_get_messages
                        (the (chans (communication_' \<Sigma>)
                               (port_channel conf (communication_' \<Sigma>)
                                 (pt (locals_' \<Sigma> ! i))))) =
                       d} \<inter>
                  \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
                  \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
                 \<lbrace>True\<rbrace> \<odot>  (- \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<and>
              (Normal \<sigma>, Normal \<sigma>n') \<in> ArincImp.Guarantee_Send_Receive i)"    
  apply (auto simp add: and_rel_def insert_message_rel port_open_insert_state_conf)
         apply (simp add: insert_message_ports Let_def  port_insert_message_def 
           port_open_def  port_exists_def )[1]
 apply (auto simp add: insert_message_ports' port_channel_def port_in_channel_def port_id_name_def port_exists_def)[2]     
     apply (auto dest:queuing_port_insert[simplified port_get_messages_def Let_def] simp:channel_get_messages_def)[1]
    apply (auto simp add: port_get_mutex_insert_message)[1]
   apply (auto simp add: alpha_ArincG_def port_full_def Let_def port_channel_def port_id_name_def port_exists_def port_in_channel_def channel_full_def)[1]
     apply (auto simp add:port_channel_def port_in_channel_def port_id_name_def port_exists_def  port_full_def channel_full_def Let_def 
                    channel_get_bufsize_def channel_get_messages_def)[1]
  by (auto simp add: guarantee_insert_channel)

lemma guarantee_insert_aux:"
  i < procs conf \<Longrightarrow>
  state_conf \<sigma>  \<Longrightarrow>  
    (Normal \<sigma>,
     Normal
      (\<sigma>\<lparr>locals_' := (locals_' \<sigma>)
         [i := (locals_' \<sigma> ! i)
            \<lparr>a_que_aux :=
               set_que_aux conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))
                (a_que_aux (locals_' \<sigma> ! i))
                (add_mset (msg (locals_' \<sigma> ! i))
                  (get_que_aux conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))
                    (a_que_aux (locals_' \<sigma> ! i))))\<rparr>]\<rparr>))
    \<in> ArincImp.Guarantee_Send_Receive i"
 unfolding Guarantee_Send_Receive_def    Guarantee_Send_Receive'_def
           set_que_aux_def get_que_aux_def state_conf_def Guarantee_mod_chan_def  
 by auto

lemma insert_aux_rel:
  assumes a0:"i < Sys_Config.procs conf" and
          a1:"(\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g" and
          a2:" state_conf \<sigma>" and                                        
          a7:"port_get_mutex conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i)) = Suc i"  
  shows "(\<sigma>\<lparr>locals_' := (locals_' \<sigma>)
         [i := (locals_' \<sigma> ! i)
            \<lparr>a_que_aux :=
               set_que_aux conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))
                (a_que_aux (locals_' \<sigma> ! i))
                (add_mset (msg (locals_' \<sigma> ! i))
                  (get_que_aux conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))
                    (a_que_aux (locals_' \<sigma> ! i))))\<rparr>]\<rparr>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g"
  using a0 a1 a2 a7
  unfolding alpha_ArincG_def state_conf_def set_que_aux_def 
port_get_mutex_def channel_get_mutex_def
  by (auto; case_tac "ia=i", auto)
  

lemma sim2_seq2_post:"
i < Sys_Config.procs conf \<Longrightarrow> 
      (\<sigma>, \<Sigma>)
       \<in> {(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>
          \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
          \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
          \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot> 
          (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
              port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i)))
               (pt (\<acute>locals ! i)) \<longrightarrow>
              p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
              p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
              \<not> snd (msg (\<acute>locals ! i))
                 \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
          ({(\<sigma>, \<Sigma>).
            a_que_aux (locals_' \<sigma> ! i)
             (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
            a_que_aux (locals_' \<Sigma> ! i)
             (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
            r_que_aux (locals_' \<sigma> ! i)
             (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
            r_que_aux (locals_' \<Sigma> ! i)
             (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))} \<inter>
           {(\<sigma>, \<Sigma>).
            \<exists>d. channel_get_messages
                 (the (chans (communication_' \<sigma>)
                        (port_channel conf (communication_' \<sigma>)
                          (pt (locals_' \<sigma> ! i))))) =
                d + {#msg (locals_' \<sigma> ! i)#} \<and>
                channel_get_messages
                 (the (chans (communication_' \<Sigma>)
                        (port_channel conf (communication_' \<Sigma>)
                          (pt (locals_' \<Sigma> ! i))))) =
                d} \<inter>
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
          \<lbrace>True\<rbrace> \<odot>  (- \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<and>
       \<sigma>' \<in> com_step
              (\<acute>locals ! i :== (\<acute>locals ! i)
               \<lparr>a_que_aux :=
                  set_que_aux conf \<acute>communication (pt (\<acute>locals ! i))
                   (a_que_aux (\<acute>locals ! i))
                   (add_mset (msg (\<acute>locals ! i))
                     (get_que_aux conf \<acute>communication (pt (\<acute>locals ! i))
                       (a_que_aux (\<acute>locals ! i))))\<rparr>)
              (Normal \<sigma>) ArincImp.\<Gamma> \<longrightarrow>
       (\<exists>\<sigma>n'. \<sigma>' = Normal \<sigma>n' \<and>
              (\<sigma>n', \<Sigma>)
              \<in> {(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>
                 \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
                 \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
                 \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot> 
                 (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                     port_id_in_part conf \<acute>communication
                      (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
                     p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                     p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                     \<not> snd (msg (\<acute>locals ! i))
                        \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
                 {(\<sigma>, \<Sigma>).
                  r_que_aux (locals_' \<sigma> ! i)
                   (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                  r_que_aux (locals_' \<Sigma> ! i)
                   (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))} \<inter>
                 {(\<sigma>, \<Sigma>).
                  \<exists>a. a_que_aux (locals_' \<Sigma> ! i)
                       (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) =
                      a \<and>
                      a_que_aux (locals_' \<sigma> ! i)
                       (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                      a + {#msg (locals_' \<sigma> ! i)#}} \<inter>
                 {(\<sigma>, \<Sigma>).
                  \<exists>d. channel_get_messages
                       (the (chans (communication_' \<sigma>)
                              (port_channel conf (communication_' \<sigma>)
                                (pt (locals_' \<sigma> ! i))))) =
                      d + {#msg (locals_' \<sigma> ! i)#} \<and>
                      channel_get_messages
                       (the (chans (communication_' \<Sigma>)
                              (port_channel conf (communication_' \<Sigma>)
                                (pt (locals_' \<Sigma> ! i))))) =
                      d} \<inter>
                 \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
                 \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter>
                 \<lbrace>True\<rbrace> \<odot>  (- \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<and>
              (Normal \<sigma>, Normal \<sigma>n') \<in> ArincImp.Guarantee_Send_Receive i)"
  apply (auto simp add: and_rel_def)               
          apply (auto simp add: and_rel_def insert_aux_rel)[1]
         apply (auto simp add: state_conf_def set_que_aux_def port_get_mutex_def get_que_aux_def)[7]
 by (auto simp add:guarantee_insert_aux)

lemma guarantee_insert_ret:"
  i < procs conf \<Longrightarrow>
  state_conf \<sigma>  \<Longrightarrow>  
    (Normal \<sigma>,
     Normal
      (\<sigma>\<lparr>locals_' := (locals_' \<sigma>)[i := (locals_' \<sigma> ! i)\<lparr>ret_n := Suc 0\<rparr>]\<rparr>))
    \<in> ArincImp.Guarantee_Send_Receive i"
 unfolding Guarantee_Send_Receive_def    Guarantee_Send_Receive'_def
           set_que_aux_def get_que_aux_def state_conf_def Guarantee_mod_chan_def  
 by auto

lemma insert_rel_rel:
  assumes a0:"i < Sys_Config.procs conf" and
          a1:"(\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g" and
          a2:" state_conf \<sigma>" and                                        
          a7:"port_get_mutex conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i)) = Suc i"  
  shows "(\<sigma>\<lparr>locals_' := (locals_' \<sigma>)[i := (locals_' \<sigma> ! i)\<lparr>ret_n := Suc 0\<rparr>]\<rparr>, \<Sigma>)  \<in> \<alpha>\<^sub>A\<^sub>g"
  using a0 a1 a2 a7
  unfolding alpha_ArincG_def 
  apply clarify
  apply (rule conjI; simp)
  apply (rule allI)
  by (case_tac "ia=i", auto simp add: state_conf_def
port_get_mutex_def channel_get_mutex_def) 
  
  
  

lemma sim2_seq3_post:"
i < Sys_Config.procs conf \<Longrightarrow> 
(\<sigma>, \<Sigma>)
       \<in> {(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>
          \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
          \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
          \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot> 
          (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
              port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i)))
               (pt (\<acute>locals ! i)) \<longrightarrow>
              p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
              p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
              \<not> snd (msg (\<acute>locals ! i))
                 \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
          {(\<sigma>, \<Sigma>).
           r_que_aux (locals_' \<sigma> ! i)
            (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
           r_que_aux (locals_' \<Sigma> ! i)
            (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))} \<inter>
          {(\<sigma>, \<Sigma>).
           \<exists>a. a_que_aux (locals_' \<Sigma> ! i)
                (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) =
               a \<and>
               a_que_aux (locals_' \<sigma> ! i)
                (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
               a + {#msg (locals_' \<sigma> ! i)#}} \<inter>
          {(\<sigma>, \<Sigma>).
           \<exists>d. channel_get_messages
                (the (chans (communication_' \<sigma>)
                       (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) =
               d + {#msg (locals_' \<sigma> ! i)#} \<and>
               channel_get_messages
                (the (chans (communication_' \<Sigma>)
                       (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))))) =
               d} \<inter>
          \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
          \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter>
          \<lbrace>True\<rbrace> \<odot>  (- \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<and>
       \<sigma>' \<in> com_step (\<acute>locals ! i :== (\<acute>locals ! i)\<lparr>ret_n := Suc 0\<rparr>) (Normal \<sigma>)
              ArincImp.\<Gamma> \<longrightarrow>
       (\<exists>\<sigma>n'. \<sigma>' = Normal \<sigma>n' \<and>
              (\<sigma>n', \<Sigma>)
              \<in> {(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>
                 \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
                 \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
                 \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot> 
                 (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                     port_id_in_part conf \<acute>communication
                      (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
                     p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                     p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                     \<not> snd (msg (\<acute>locals ! i))
                        \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
                 {(\<sigma>, \<Sigma>).
                  r_que_aux (locals_' \<sigma> ! i)
                   (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                  r_que_aux (locals_' \<Sigma> ! i)
                   (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))} \<inter>
                 {(\<sigma>, \<Sigma>).
                  \<exists>a. a_que_aux (locals_' \<Sigma> ! i)
                       (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) =
                      a \<and>
                      a_que_aux (locals_' \<sigma> ! i)
                       (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                      a + {#msg (locals_' \<sigma> ! i)#}} \<inter>
                 {(\<sigma>, \<Sigma>).
                  \<exists>d. channel_get_messages
                       (the (chans (communication_' \<sigma>)
                              (port_channel conf (communication_' \<sigma>)
                                (pt (locals_' \<sigma> ! i))))) =
                      d + {#msg (locals_' \<sigma> ! i)#} \<and>
                      channel_get_messages
                       (the (chans (communication_' \<Sigma>)
                              (port_channel conf (communication_' \<Sigma>)
                                (pt (locals_' \<Sigma> ! i))))) =
                      d} \<inter>
                 \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
                 \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter>
                 \<lbrace>True\<rbrace> \<odot>  (- \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
                 \<lbrace>ret_n (\<acute>locals ! i) = Suc 0\<rbrace> \<odot>  \<lbrace>True\<rbrace> \<and>
              (Normal \<sigma>, Normal \<sigma>n') \<in> ArincImp.Guarantee_Send_Receive i)"
  apply (auto simp add: and_rel_def)               
          apply (auto simp add: and_rel_def insert_rel_rel)[1]
         apply (auto simp add: state_conf_def set_que_aux_def port_get_mutex_def get_que_aux_def)[8]
 by (auto simp add:guarantee_insert_ret)


lemma p_q:"(\<sigma>n, b) \<in> \<alpha>\<^sub>A\<^sub>g \<Longrightarrow> 
        p_queuing conf (communication_' b) (pt (locals_' b ! i)) \<Longrightarrow>
        p_queuing conf (communication_' \<sigma>n) (pt (locals_' \<sigma>n ! i))
      "
 unfolding alpha_ArincG_def p_queuing_def port_channel_def 
           port_in_channel_def port_id_name_def port_exists_def
  by auto

lemma guarantee_send_message: " i < Sys_Config.procs conf \<Longrightarrow>       
       state_conf
        \<lparr>communication_' = ca, locals_' = la, timer_' = ta\<rparr> \<Longrightarrow>
       port_get_mutex conf ca (pt (la ! i)) = Suc i \<Longrightarrow>
       p_source conf ca (pt (la ! i)) \<Longrightarrow>
       p_queuing conf ca (pt (la ! i)) \<Longrightarrow>
       port_open ca (pt (la ! i)) \<Longrightarrow>
       port_id_in_part conf ca (current (schedule (la ! i)))
        (pt (la ! i)) \<Longrightarrow>
       \<not> port_full conf ca (pt (la ! i)) \<Longrightarrow>                           
       (Normal \<lparr>communication_' =ca, locals_' = la, timer_' = ta\<rparr>,
        Normal
         \<lparr>communication_' =
            port_set_mutex conf
             (port_insert_message conf ca (pt (la ! i))
               (msg (la ! i)) 0)
             (pt (la
                  [i := (la ! i)
                     \<lparr>a_que_aux :=
                        set_que_aux conf
                         (port_insert_message conf ca (pt (la ! i))
                           (msg (la ! i)) 0)
                         (pt (la ! i)) (a_que_aux (la ! i))
                         (add_mset (msg (la! i))
                           (get_que_aux conf
                             (port_insert_message conf ca (pt (la ! i))
                               (msg (la ! i)) 0)
                             (pt (la ! i)) (a_que_aux (la ! i))))\<rparr>] !
                  i))
             0,
            locals_' = la
              [i := (la
                     [i := (la ! i)
                        \<lparr>a_que_aux :=
                           set_que_aux conf
                            (port_insert_message conf ca (pt (la ! i))
                              (msg (la ! i)) 0)
                            (pt (la ! i)) (a_que_aux (la ! i))
                            (add_mset (msg (la ! i))
                              (get_que_aux conf
                                (port_insert_message conf ca
                                  (pt (localsa ! i)) (msg (la ! i)) 0)
                                (pt (la ! i)) (a_que_aux (la ! i))))\<rparr>] !
                     i)
                 \<lparr>ret_n := Suc 0\<rparr>],
            timer_' = ta\<rparr>)
       \<in> ArincQueuing.Guarantee_Send_Receive i"
  
 unfolding ArincQueuing.Guarantee_Send_Receive_def  ArincQueuing.Guarantee_Send_Receive'_def
             port_get_mutex_def channel_get_mutex_def set_que_aux_def get_que_aux_def channel_set_messages_def 
          channel_insert_message_def Let_def port_insert_message_def channel_set_mutex_def 
          port_set_mutex_def state_conf_def Invariant_def chan_queuing_def chan_sampling_def
          channel_get_messages_def port_full_def channel_full_def
             channel_get_bufsize_def  ArincQueuing.Guarantee_mod_chan_def  
             p_queuing_def   ch_id_queuing_def  port_exists_def 
        apply (case_tac "data (the (chans ca (port_channel conf ca (pt (la ! i)))))")   
       unfolding port_channel_def port_in_channel_def  port_id_name_def port_exists_def
    apply auto   
   unfolding state_conf_def chan_queuing_def port_open_def chan_sampling_def not_less_eq_eq 
     port_channel_def port_in_channel_def port_name_in_channel_def port_id_name_def port_exists_def    
   apply auto
   by (metis get_channel_def only_ch_ch_id)+

lemma eq_port_channel: "ports (communication_' \<sigma>) = ports (communication_' \<sigma>') \<Longrightarrow>
       pt(locals_' \<sigma>!i) = pt (locals_' \<sigma>' !i) \<Longrightarrow>
         port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma>!i)) = 
         port_channel conf (communication_' \<sigma>') (pt (locals_' \<sigma>'!i))"
  unfolding port_channel_def port_in_channel_def port_id_name_def port_exists_def
  by auto

lemma eq_port_channel': "ports c = ports ca \<Longrightarrow>
       pt(l!i) = pt (la !i) \<Longrightarrow>
         port_channel conf c (pt (l!i)) = 
         port_channel conf ca (pt (la!i))"
  unfolding port_channel_def port_in_channel_def port_id_name_def port_exists_def
  by auto
lemma l1:" chans c (port_channel conf c pt_id) = Some ch1 \<and> chan_queuing ch1 \<Longrightarrow>
       \<exists>q. data (the (chans c (port_channel conf c pt_id))) = Queue q"
  unfolding chan_queuing_def chan_sampling_def
  by (metis (no_types) Channel_data.exhaust Channel_data.simps(5) option.sel)

lemma rel_send_message:
  assumes a0:"  i < Sys_Config.procs conf " and
 a1:"(\<lparr>communication_' = c, locals_' = l, timer_' = t\<rparr>,
        \<lparr>communication_' = ca, locals_' = la, timer_' = ta\<rparr>)
       \<in> \<alpha>\<^sub>A\<^sub>g" and
 a2: "port_open c (pt (l ! i))" and
 a3: "port_open ca (pt (la ! i))" and
 a4:"p_queuing conf ca (pt (la ! i))" and 
 a5:"r_que_aux (l ! i) (port_channel conf c (pt (l ! i))) =
       r_que_aux (la ! i) (port_channel conf ca (pt (la ! i)))" and
 a6:"a_que_aux (l ! i) (port_channel conf c (pt (l ! i))) =
       add_mset (msg (l ! i))
        (a_que_aux (la ! i)
          (port_channel conf ca (pt (la ! i))))" and
 a7:"channel_get_messages
        (the (chans c
               (port_channel conf c (pt (l! i))))) =
       add_mset (msg (l ! i))
        (channel_get_messages
          (the (chans ca
                 (port_channel conf ca (pt (la ! i))))))" and
 a8:"port_get_mutex conf c (pt (l ! i)) = Suc i" and
 a9:"port_get_mutex conf ca (pt (la ! i)) = Suc i " and
 a10:"ret_n (l ! i) = Suc 0" and
 a11:"state_conf
        \<lparr>communication_' = ca, locals_' = la, timer_' = ta\<rparr>" and
 a12:"\<not> port_full conf ca (pt (la ! i))" and
 a13:"\<sigma> = \<lparr>communication_' = port_set_mutex conf c (pt (l ! i)) 0,
           locals_' = l, timer_' = t\<rparr>" and
 a14:"\<Sigma> = \<lparr>communication_' =
           port_set_mutex conf
            (port_insert_message conf ca (pt (la ! i))
              (msg (la ! i)) 0)
            (pt (la
                 [i := (la ! i)
                    \<lparr>a_que_aux :=
                       set_que_aux conf
                        (port_insert_message conf ca (pt (la ! i))
                          (msg (la ! i)) 0)
                        (pt (la ! i)) (a_que_aux (la ! i))
                        (add_mset (msg (la ! i))
                          (get_que_aux conf
                            (port_insert_message conf ca (pt (la ! i))
                              (msg (la ! i)) 0)
                            (pt (la ! i)) (a_que_aux (la ! i))))\<rparr>] !
                 i))
            0,
           locals_' = la
             [i := (la
                    [i := (la ! i)
                       \<lparr>a_que_aux :=
                          set_que_aux conf
                           (port_insert_message conf ca (pt (la ! i))
                             (msg (la ! i)) 0)
                           (pt (la ! i)) (a_que_aux (la ! i))
                           (add_mset (msg (la ! i))
                             (get_que_aux conf
                               (port_insert_message conf ca
                                 (pt (la ! i)) (msg (la ! i)) 0)
                               (pt (la ! i)) (a_que_aux (la ! i))))\<rparr>] !
                    i)
                \<lparr>ret_n := Suc 0\<rparr>],
           timer_' = ta\<rparr>" 
shows "(\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g"
proof-
  have eq_ports_c_ca:"ports c = ports ca"
    using a1 unfolding alpha_ArincG_def by auto
  have ports_c:"ports c = ports (communication_' \<sigma>)"
    using a13 unfolding port_set_mutex_def Let_def by auto
  have ports_ca:"ports ca = ports (communication_' \<Sigma>)"
    using a14 unfolding port_set_mutex_def Let_def port_insert_message_def channel_insert_message_def by auto      
     
  have a11':"state_conf
            \<lparr>communication_' = c, locals_' = l, timer_' = t\<rparr>"
    using a1 a11
    using ArincRefinement.a2 by auto  
  then have a0la : "i<length la" and a0l: "i<length l" 
    using a0 a11 unfolding state_conf_def by auto 
  then have a14:"\<Sigma> = \<lparr>communication_' =
           port_set_mutex conf
            (port_insert_message conf ca (pt (la ! i)) (msg (la ! i)) 0)
            (pt (la ! i)) 0,
           locals_' = la
             [i := (la
                    [i := (la ! i)
                       \<lparr>a_que_aux :=
                          set_que_aux conf ca
                           (pt (la ! i)) (a_que_aux (la ! i))
                           (add_mset (msg (la ! i))
                             (get_que_aux conf ca
                               (pt (la ! i)) (a_que_aux (la ! i))))\<rparr>] !
                    i)
                \<lparr>ret_n := Suc 0\<rparr>],
           timer_' = ta\<rparr>"
    using a14 unfolding set_que_aux_def get_que_aux_def
           Let_def port_insert_message_def port_exists_def                                  
     port_channel_def port_in_channel_def  port_id_name_def set_que_aux_def
    by auto   
 
    
  have l:"(locals_' \<sigma>) = l" by (simp add: a13)     
  then have mut_\<sigma>:"port_get_mutex conf (communication_' \<sigma>) (pt (locals_' \<sigma>!i)) = 0"
    using a13
    by (metis  port_get_set_mutex vars.select_convs(1)) 
  have pt:"pt (locals_' \<Sigma>!i) = pt (la !i)" 
    using a14 a0la unfolding set_que_aux_def Let_def by auto
  have ptl:"pt (locals_' \<sigma>!i) = pt (l!i)"
    using a13 by auto
  have pt_eq:"pt (l!i) = pt (la!i)" 
    using a1 unfolding alpha_ArincG_def by auto
  moreover have mut_ca:"communication_' \<Sigma> =(port_set_mutex conf
            (port_insert_message conf ca (pt (la ! i)) (msg (la ! i)) 0) (pt (la ! i))
            0)" using a14 by auto
  moreover have mut_c:"port_get_mutex conf (port_set_mutex conf
            (port_insert_message conf ca (pt (la ! i)) (msg (la ! i)) 0) (pt (la ! i))
            0) (pt (locals_' \<Sigma>!i)) = 0" using pt port_get_set_mutex by auto    
  ultimately have mut_\<Sigma>:
    "port_get_mutex conf (communication_' \<Sigma>) (pt (locals_' \<Sigma>!i)) = 0"
    by auto
  have port_channel_c_ca:"port_channel conf ca (pt (la ! i)) = port_channel conf c (pt (l ! i))"
    using pt_eq ports_c ports_ca eq_ports_c_ca eq_port_channel'
    by metis
  have port_channel_\<sigma>_\<Sigma>:"port_channel conf (communication_' \<sigma>) (pt (la ! i)) = 
                         port_channel conf (communication_' \<Sigma>) (pt (l ! i))"
   using eq_port_channel'
   using eq_ports_c_ca ports_c ports_ca pt_eq by fastforce

  have port_channel_c_\<sigma>:"port_channel conf (communication_' \<sigma>) (pt (l ! i)) = 
                         port_channel conf c (pt (l ! i))"
   using eq_port_channel'
   using ports_c ports_c ports_ca pt_eq by fastforce

  have port_channel_ca_\<Sigma>:"port_channel conf (communication_' \<Sigma>) (pt (la ! i)) = 
                         port_channel conf ca (pt (la ! i))"
   using eq_port_channel'
   using ports_c ports_c ports_ca pt_eq by fastforce

  have c_messages:"port_get_messages conf (communication_' \<sigma>) (pt (locals_' \<sigma>!i)) = 
             port_get_messages conf c (pt (l !i)) "
    using a13 a4 unfolding port_set_mutex_def 
        Let_def port_get_mutex_def channel_get_mutex_def channel_set_mutex_def port_channel_def
        port_in_channel_def port_id_name_def port_exists_def
    port_get_messages_def channel_get_messages_def 
    by auto
  
  have p_queue:"p_queuing conf c (pt (l ! i))" 
    using a1 a4
    using p_q by fastforce
  have chan_queuing_c:"\<exists>chan. chans c (port_channel conf c (pt (l ! i))) = Some chan \<and>
                              chan_queuing chan"
  proof-
    have "port_in_channel conf c (pt (l ! i)) (port_channel conf c (pt (l ! i)))"
      using a11' local.a2 port_unique_channel by fastforce
    thus ?thesis using p_queuing_chan_queuing[OF a11' _ _] a2 p_queue by auto
  qed
  then have chan_queuing_c:"\<exists>chan. chans (communication_' \<sigma>) (port_channel conf c (pt (l ! i))) = Some chan \<and>
                              chan_queuing chan"
    using a13 unfolding port_set_mutex_def Let_def channel_set_mutex_def
    chan_queuing_def chan_sampling_def by auto

  have chans_c:"\<forall>ch. ch \<noteq> port_channel conf c (pt (l!i)) \<longrightarrow> 
           chans (communication_' \<sigma>) ch = chans c ch"
    using a13 unfolding port_set_mutex_def Let_def channel_set_mutex_def by auto
  then have chans_ca:"\<forall>ch. ch \<noteq> port_channel conf ca (pt (la!i)) \<longrightarrow>
           chans (communication_' \<Sigma>) ch = chans ca ch"
    using a14 unfolding  port_set_mutex_def Let_def 
        port_insert_message_def channel_set_mutex_def channel_insert_message_def
        channel_get_messages_def channel_set_messages_def 
      apply auto 
      apply (case_tac "data (the (chans ca (port_channel conf ca (pt (la ! i)))))")
      unfolding port_channel_def port_in_channel_def port_id_name_def port_exists_def
      by auto
  have "length (locals_' \<sigma>) = length (locals_' \<Sigma>)"
  proof-
    have "length l = length la" using a1 unfolding alpha_ArincG_def by auto
    thus ?thesis
      using a13 a14 by auto
  qed
  moreover have "\<forall>i. evnt ((locals_' \<sigma>)!i) = evnt ((locals_' \<Sigma>)!i) \<and> 
              pt ((locals_' \<sigma>)!i) = pt ((locals_' \<Sigma>)!i) \<and>
              msg ((locals_' \<sigma>)!i) = msg ((locals_' \<Sigma>)!i) \<and>
              schedule ((locals_' \<sigma>)!i) = schedule ((locals_' \<Sigma>)!i) \<and>
              ret_msg ((locals_' \<sigma>)!i) = ret_msg ((locals_' \<Sigma>)!i) \<and>
              (mut (the (chans (communication_' \<sigma>) 
                (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> !i))))) \<noteq> i+1 \<longrightarrow>
                  ret_n ((locals_' \<sigma>)!i) = ret_n ((locals_' \<Sigma>)!i)) \<and>              
                  (\<forall>ch_id.                  
                    mut (the (chans (communication_' \<sigma>) ch_id)) \<noteq> i+1 \<longrightarrow> 
                        a_que_aux ((locals_' \<sigma>)!i) ch_id = a_que_aux ((locals_' \<Sigma>)!i) ch_id \<and>
                        r_que_aux ((locals_' \<sigma>)!i) ch_id = r_que_aux ((locals_' \<Sigma>)!i) ch_id)" 
  proof-
    {fix j
      {assume a00:"i\<noteq>j"
        then have la:"locals_' \<Sigma> ! j = la!j"
          using a14 by auto
        then have "evnt (locals_' \<sigma> ! j) = evnt (locals_' \<Sigma> ! j) \<and>
             pt (locals_' \<sigma> ! j) = pt (locals_' \<Sigma> ! j) \<and>
             msg (locals_' \<sigma> ! j) = msg (locals_' \<Sigma> ! j) \<and>
             schedule (locals_' \<sigma> ! j) = schedule (locals_' \<Sigma> ! j) \<and>
             ret_msg (locals_' \<sigma> ! j) = ret_msg (locals_' \<Sigma> ! j)" 
          using a1 l unfolding alpha_ArincG_def by auto
        moreover {assume a01:"mut (the (chans (communication_' \<sigma>)
                    (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! j))))) \<noteq>
                 j + 1"
         {assume a02: "(port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! j))) = 
                       (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i)))"          
           then have "port_channel conf c (pt (l! j)) = 
                       port_channel conf c (pt (l ! i))"
             using  l ports_c a13
             by (metis port_channl_eq_ports vars.select_convs(1))                       
           then have "ret_n (l ! j) = ret_n (la ! j)" using a1 
             using a00 a8 unfolding alpha_ArincG_def  
             port_get_mutex_def Let_def channel_get_mutex_def by auto
           then have "ret_n (locals_' \<sigma> ! j) = ret_n (locals_' \<Sigma> ! j)" 
             using l la by auto 
         }
         moreover {assume a02: 
                      "(port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! j))) \<noteq>
                       (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i)))" 
           then have "port_channel conf c (pt (l! j)) \<noteq>
                       port_channel conf c (pt (l ! i))"
             using  l ports_c a13
             by (metis port_channl_eq_ports vars.select_convs(1))
           then have "mut (the (chans c (port_channel conf c (pt (l! j))))) = 
                      mut (the (chans (communication_' \<sigma>) (port_channel conf c (pt (l! j)))))"
             using a01 a13 l unfolding port_set_mutex_def Let_def channel_set_mutex_def by auto
           then have "mut (the (chans c (port_channel conf c (pt (l! j))))) = 
                      mut (the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! j)))))"
              using eq_port_channel ports_c a13 l
              by (metis (no_types, lifting) vars.select_convs(1) vars.select_convs(2)) 
            then have "ret_n (l!j) = ret_n (la ! j)" using a1 a01 unfolding alpha_ArincG_def by auto
            then have "ret_n (locals_' \<sigma> ! j) = ret_n (locals_' \<Sigma> ! j)"
              using l la by auto
         }           
         ultimately have "ret_n (locals_' \<sigma> ! j) = ret_n (locals_' \<Sigma> ! j)"
           by auto
       }
       then have "(mut (the (chans (communication_' \<sigma>) 
                (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> !j))))) \<noteq> j+1 \<longrightarrow>
                  ret_n ((locals_' \<sigma>)!j) = ret_n ((locals_' \<Sigma>)!j))" by auto
       moreover 
       {fix ch_id
         assume a01: "mut (the (chans (communication_' \<sigma>) ch_id)) \<noteq> j+1"
         {assume a02: "ch_id = (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i)))"
           then have "mut (the (chans c ch_id)) = i+1 " 
             using a8 ports_c l  a13
             unfolding port_get_mutex_def Let_def channel_get_mutex_def
             by (metis Suc_eq_plus1 port_channl_eq_pid vars.select_convs(1))
           then have "mut (the (chans c ch_id)) \<noteq> j+1 " using a00 by auto           
           then have "a_que_aux ((locals_' \<sigma>)!j) ch_id = a_que_aux ((locals_' \<Sigma>)!j) ch_id \<and>
                    r_que_aux ((locals_' \<sigma>)!j) ch_id = r_que_aux ((locals_' \<Sigma>)!j) ch_id"
           using a1 l la unfolding alpha_ArincG_def by auto
         }
         moreover {assume a02: "ch_id \<noteq> (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i)))"
           then have "ch_id \<noteq> (port_channel conf c (pt (l ! i)))"
             using a8 ports_c l a13 
             by (metis  port_channl_eq_pid vars.select_convs(1))
           then have "mut (the (chans c ch_id)) = mut (the (chans (communication_' \<sigma>) ch_id))" 
             using a13 ports  unfolding port_set_mutex_def port_get_mutex_def Let_def channel_get_mutex_def             
             by auto          
           then have "a_que_aux ((locals_' \<sigma>)!j) ch_id = a_que_aux ((locals_' \<Sigma>)!j) ch_id \<and>
                    r_que_aux ((locals_' \<sigma>)!j) ch_id = r_que_aux ((locals_' \<Sigma>)!j) ch_id"
           using a01 a1 l la unfolding alpha_ArincG_def by auto
         } ultimately have "a_que_aux ((locals_' \<sigma>)!j) ch_id = a_que_aux ((locals_' \<Sigma>)!j) ch_id \<and>
                    r_que_aux ((locals_' \<sigma>)!j) ch_id = r_que_aux ((locals_' \<Sigma>)!j) ch_id" by auto

       } then have "\<forall>ch_id. mut (the (chans (communication_' \<sigma>) ch_id)) \<noteq> j + 1 \<longrightarrow>
                      a_que_aux (locals_' \<sigma> ! j) ch_id = a_que_aux (locals_' \<Sigma> ! j) ch_id \<and>
                      r_que_aux (locals_' \<sigma> ! j) ch_id = r_que_aux (locals_' \<Sigma> ! j) ch_id " 
         by auto
        ultimately have "evnt ((locals_' \<sigma>)!j) = evnt ((locals_' \<Sigma>)!j) \<and> 
              pt ((locals_' \<sigma>)!j) = pt ((locals_' \<Sigma>)!j) \<and>
              msg ((locals_' \<sigma>)!j) = msg ((locals_' \<Sigma>)!j) \<and>
              schedule ((locals_' \<sigma>)!j) = schedule ((locals_' \<Sigma>)!j) \<and>
              ret_msg ((locals_' \<sigma>)!j) = ret_msg ((locals_' \<Sigma>)!j) \<and>
              (mut (the (chans (communication_' \<sigma>) 
                (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> !j))))) \<noteq> j+1 \<longrightarrow>
                  ret_n ((locals_' \<sigma>)!j) = ret_n ((locals_' \<Sigma>)!j)) \<and>              
              (\<forall>ch_id.                  
                mut (the (chans (communication_' \<sigma>) ch_id)) \<noteq> j+1 \<longrightarrow> 
                    a_que_aux ((locals_' \<sigma>)!j) ch_id = a_que_aux ((locals_' \<Sigma>)!j) ch_id \<and>
                    r_que_aux ((locals_' \<sigma>)!j) ch_id = r_que_aux ((locals_' \<Sigma>)!j) ch_id)"
          by auto
      }
      moreover{ assume a00:"i=j"
        have vars:"evnt (l!j) = evnt (la!j) \<and> 
              pt (l!j) = pt (la!j) \<and>
              msg (l!j) = msg (la!j) \<and>
              schedule (l!j) = schedule (la!j) \<and>
              ret_msg (l!j) = ret_msg (la!j)"
          using a1 unfolding alpha_ArincG_def by auto
        then have "evnt ((locals_' \<sigma>)!j) = evnt ((locals_' \<Sigma>)!j) \<and> 
              pt ((locals_' \<sigma>)!j) = pt ((locals_' \<Sigma>)!j) \<and>
              msg ((locals_' \<sigma>)!j) = msg ((locals_' \<Sigma>)!j) \<and>
              schedule ((locals_' \<sigma>)!j) = schedule ((locals_' \<Sigma>)!j) \<and>
              ret_msg ((locals_' \<sigma>)!j) = ret_msg ((locals_' \<Sigma>)!j)"          
          using l  a14 a00 a0la unfolding set_que_aux_def Let_def by auto
        moreover{
          assume "mut (the (chans (communication_' \<sigma>) 
                (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> !j))))) \<noteq> j+1"         
          then have "ret_n ((locals_' \<sigma>)!j) = ret_n ((locals_' \<Sigma>)!j)"
            using a00  a13 a14  a10  a0la 
            unfolding set_que_aux_def Let_def by auto            
        }
        moreover{
         {fix ch_id
           assume a01: "mut (the (chans (communication_' \<sigma>) ch_id)) \<noteq> j+1"
           {assume a02: "ch_id = (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i)))"
             have pt0:"(port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) = ch_id"
               using eq_ports_c_ca ports_c ports_ca pt eq_port_channel
               by (metis a00 a02 calculation(1))
             have pt1:"port_channel conf c (pt (l!i)) = (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i)))" 
               using  ports_c l
               by (metis port_channl_eq_pid  vars.select_convs(1))
             have pt2:"port_channel conf ca (pt (la!i)) = (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))"
               using  ports_ca pt 
               by (metis   port_channl_eq_pid ports_ca vars.select_convs(1))
             have "r_que_aux ((locals_' \<Sigma>)!j) ch_id = r_que_aux (la!j) ch_id "
               using a14 a0la unfolding set_que_aux_def Let_def a00  by auto
             then have "r_que_aux ((locals_' \<sigma>)!j) ch_id = r_que_aux ((locals_' \<Sigma>)!j) ch_id"
               using a5 a00  ports_c ports_ca pt eq_port_channel eq_port_channel l
               by (metis a02 calculation(1) eq_ports_c_ca vars.select_convs(1) vars.select_convs(2)) 
             moreover have "a_que_aux ((locals_' \<sigma>)!j) ch_id = a_que_aux ((locals_' \<Sigma>)!j) ch_id"
             proof-
               have "a_que_aux ((locals_' \<Sigma>)!j) ch_id = add_mset (msg (la ! i)) (a_que_aux (la ! i) (port_channel conf ca (pt (la ! i))))"
                 using a14 a0la a02 pt0  pt2 ports_ca pt a00 
                 unfolding set_que_aux_def Let_def  get_que_aux_def  by auto
               moreover have "a_que_aux (l ! i) (port_channel conf c (pt (l ! i))) = 
                              a_que_aux (locals_' \<sigma> ! i) 
                                (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i)))"
                 using a13 unfolding port_set_mutex_def Let_def channel_set_mutex_def l pt1 by auto
               ultimately show ?thesis using a6 a02 a00
                 by (simp add: vars) 
             qed
             ultimately have "a_que_aux ((locals_' \<sigma>)!j) ch_id = a_que_aux ((locals_' \<Sigma>)!j) ch_id \<and>
                    r_que_aux ((locals_' \<sigma>)!j) ch_id = r_que_aux ((locals_' \<Sigma>)!j) ch_id"
               by auto
           }         
           moreover {assume a02: "ch_id \<noteq> (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i)))"
           then have pc_ch_id:"ch_id \<noteq> (port_channel conf c (pt (l ! i)))"
             using a8 ports_c l a13 
             by (metis  port_channl_eq_pid vars.select_convs(1))
           then have pc_ch_ida:"ch_id \<noteq> (port_channel conf ca (pt (la ! i)))"
             using ports_ca pt
             by (metis a00 eq_ports_c_ca port_channl_eq_pid vars vars.select_convs(1))
           then have "mut (the (chans c ch_id)) = mut (the (chans (communication_' \<sigma>) ch_id))"
             using pc_ch_id a13 unfolding port_set_mutex_def Let_def channel_set_mutex_def by auto
           then have "mut (the (chans c ch_id)) \<noteq> j+1 " using a01 by auto
           then have "a_que_aux (l!j) ch_id = a_que_aux (la!j) ch_id \<and>
                      r_que_aux (l!j) ch_id = r_que_aux (la!j) ch_id"
             using a1 unfolding alpha_ArincG_def by auto
           moreover have "a_que_aux (l!j) ch_id = a_que_aux (locals_' \<sigma>!j) ch_id \<and>
                          r_que_aux (l!j) ch_id = r_que_aux (locals_' \<sigma>!j) ch_id"
             using l by auto
           moreover have "a_que_aux (la!j) ch_id = a_que_aux (locals_' \<Sigma>!j) ch_id \<and>
                          r_que_aux (la!j) ch_id = r_que_aux (locals_' \<Sigma>!j) ch_id"
             using a00 a14 a0la a02 ports_ca pt pc_ch_ida unfolding set_que_aux_def Let_def get_que_aux_def 
             by auto
           ultimately have "a_que_aux ((locals_' \<sigma>)!j) ch_id = a_que_aux ((locals_' \<Sigma>)!j) ch_id \<and>
                    r_que_aux ((locals_' \<sigma>)!j) ch_id = r_que_aux ((locals_' \<Sigma>)!j) ch_id"
             by auto           
         } ultimately have "a_que_aux ((locals_' \<sigma>)!j) ch_id = a_que_aux ((locals_' \<Sigma>)!j) ch_id \<and>
                    r_que_aux ((locals_' \<sigma>)!j) ch_id = r_que_aux ((locals_' \<Sigma>)!j) ch_id" by auto
       } then have "\<forall>ch_id. mut (the (chans (communication_' \<sigma>) ch_id)) \<noteq> j + 1 \<longrightarrow>
                      a_que_aux (locals_' \<sigma> ! j) ch_id = a_que_aux (locals_' \<Sigma> ! j) ch_id \<and>
                      r_que_aux (locals_' \<sigma> ! j) ch_id = r_que_aux (locals_' \<Sigma> ! j) ch_id " 
         by auto          
        }
        ultimately have "evnt ((locals_' \<sigma>)!j) = evnt ((locals_' \<Sigma>)!j) \<and> 
              pt ((locals_' \<sigma>)!j) = pt ((locals_' \<Sigma>)!j) \<and>
              msg ((locals_' \<sigma>)!j) = msg ((locals_' \<Sigma>)!j) \<and>
              schedule ((locals_' \<sigma>)!j) = schedule ((locals_' \<Sigma>)!j) \<and>
              ret_msg ((locals_' \<sigma>)!j) = ret_msg ((locals_' \<Sigma>)!j) \<and>
              (mut (the (chans (communication_' \<sigma>) 
                (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> !j))))) \<noteq> j+1 \<longrightarrow>
                  ret_n ((locals_' \<sigma>)!j) = ret_n ((locals_' \<Sigma>)!j)) \<and>              
              (\<forall>ch_id.                  
                mut (the (chans (communication_' \<sigma>) ch_id)) \<noteq> j+1 \<longrightarrow> 
                    a_que_aux ((locals_' \<sigma>)!j) ch_id = a_que_aux ((locals_' \<Sigma>)!j) ch_id \<and>
                    r_que_aux ((locals_' \<sigma>)!j) ch_id = r_que_aux ((locals_' \<Sigma>)!j) ch_id)"
          by auto
      } ultimately have "evnt ((locals_' \<sigma>)!j) = evnt ((locals_' \<Sigma>)!j) \<and> 
              pt ((locals_' \<sigma>)!j) = pt ((locals_' \<Sigma>)!j) \<and>
              msg ((locals_' \<sigma>)!j) = msg ((locals_' \<Sigma>)!j) \<and>
              schedule ((locals_' \<sigma>)!j) = schedule ((locals_' \<Sigma>)!j) \<and>
              ret_msg ((locals_' \<sigma>)!j) = ret_msg ((locals_' \<Sigma>)!j) \<and>
              (mut (the (chans (communication_' \<sigma>) 
                (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> !j))))) \<noteq> j+1 \<longrightarrow>
                  ret_n ((locals_' \<sigma>)!j) = ret_n ((locals_' \<Sigma>)!j)) \<and>              
              (\<forall>ch_id.                  
                mut (the (chans (communication_' \<sigma>) ch_id)) \<noteq> j+1 \<longrightarrow> 
                    a_que_aux ((locals_' \<sigma>)!j) ch_id = a_que_aux ((locals_' \<Sigma>)!j) ch_id \<and>
                    r_que_aux ((locals_' \<sigma>)!j) ch_id = r_que_aux ((locals_' \<Sigma>)!j) ch_id)"
        by auto
    }
   then show ?thesis  by auto
  qed
  moreover have "ports (communication_' \<sigma>) = ports (communication_' \<Sigma>)"
    using ports_ca ports_c eq_ports_c_ca by auto
  moreover have "{ch. chans (communication_' \<sigma>) ch = None} = 
             {ch. chans (communication_' \<Sigma>) ch = None}"
  proof-    
    {fix ch
      assume a00:"chans (communication_' \<sigma>) ch = \<tau>"     
      {assume a01:"ch = port_channel conf c (pt (l!i))"
        have "chans c (port_channel conf c (pt (l!i))) \<noteq> \<tau>"
          using a3 a11
          using a11' local.a2 port_open_queuing_some_chan by fastforce
        then have "chans (communication_' \<sigma>) ch \<noteq> \<tau>"
          using a01 a13 unfolding port_set_mutex_def Let_def channel_set_mutex_def
          by auto
        then have "chans (communication_' \<Sigma>) ch = \<tau>" using a00 by auto        
      }
      moreover 
      {assume a01:"ch \<noteq> port_channel conf c (pt (l!i))"
        then have "chans c ch = \<tau>" using chans_c a00 by auto
        then have "chans ca ch = \<tau>" using  a1 unfolding alpha_ArincG_def
          by auto
        then have "chans (communication_' \<Sigma>) ch = \<tau>" 
          using chans_ca port_channel_c_ca a01 by auto
      } ultimately have "chans (communication_' \<Sigma>) ch = \<tau>" by fastforce
    } then have  "{ch. chans (communication_' \<sigma>) ch = \<tau>} \<subseteq> {ch. chans (communication_' \<Sigma>) ch = \<tau>}"
      by auto
    moreover {
      fix ch
      assume a00:"chans (communication_' \<Sigma>) ch = \<tau>"     
      {assume a01:"ch = port_channel conf c (pt (l!i))"        
        then have "chans ca ch \<noteq> \<tau>" using port_channel_c_ca unfolding alpha_ArincG_def
          using a11 local.a3 port_open_queuing_some_chan by fastforce
        then have "chans (communication_' \<Sigma>) ch \<noteq> \<tau>"
          using a14 a01 a00 unfolding port_insert_message_def Let_def port_set_mutex_def 
           channel_insert_message_def channel_set_messages_def channel_get_messages_def
           channel_set_mutex_def
          apply auto
          apply (case_tac " data (the (chans ca (port_channel conf ca (pt (la ! i)))))")
          apply auto
           apply (smt fun_upd_same option.distinct(1) port_channel_c_ca)
          by (smt fun_upd_same option.distinct(1) port_channel_c_ca)
        then have "chans (communication_' \<sigma>) ch = \<tau>" using a00 by auto        
      }
      moreover 
      {assume a01:"ch \<noteq> port_channel conf c (pt (l!i))"
        then have "chans ca ch = \<tau>" using chans_ca a00 port_channel_c_ca by auto        
        then have "chans c ch = \<tau>" using a1 unfolding alpha_ArincG_def
          by auto
        then have "chans (communication_' \<sigma>) ch = \<tau>" 
          using chans_c port_channel_c_ca a01 by auto
      } ultimately have "chans (communication_' \<sigma>) ch = \<tau>" by fastforce
    }then have  "{ch. chans (communication_' \<Sigma>) ch = \<tau>} \<subseteq> {ch. chans (communication_' \<sigma>) ch = \<tau>}"
      by auto
    ultimately show ?thesis by auto
  qed
 moreover have  eq_types:"{ch. \<exists>ch1. chans (communication_' \<sigma>) ch = Some ch1 \<and> chan_queuing ch1} = 
              {ch. \<exists>ch1. chans (communication_' \<Sigma>) ch = Some ch1 \<and> chan_queuing ch1}"
 proof-    
    {fix ch
      assume a00:"\<exists>ch1. chans (communication_' \<sigma>) ch = Some ch1 \<and> chan_queuing ch1"
      then obtain ch1 where a00:"chans (communication_' \<sigma>) ch = Some ch1 \<and> chan_queuing ch1" 
        by auto
      {assume a01:"ch = port_channel conf c (pt (l!i))"
        then obtain ch1 where css:"chans ca ch = Some ch1 \<and> chan_queuing ch1"
          using a3 a11 a4 port_channel_c_ca
          using port_open_queuing_some_chan_queuing by fastforce               
        then have "\<exists>ch1. chans (communication_' \<Sigma>) ch = Some ch1 \<and> chan_queuing ch1" 
          using a14 l1 port_channel_c_ca unfolding port_set_mutex_def Let_def channel_set_mutex_def
         port_insert_message_def channel_insert_message_def channel_set_messages_def
         channel_get_messages_def chan_queuing_def chan_sampling_def
          apply auto 
          apply (case_tac " data (the (chans ca (port_channel conf ca (pt (la ! i)))))")
          by auto
      }
      moreover 
      {assume a01:"ch \<noteq> port_channel conf c (pt (l!i))"
        then have "chans c ch = Some ch1 \<and> chan_queuing ch1" 
          using chans_c a00 by auto
        then have "\<exists>ch1. chans ca ch = Some ch1 \<and> chan_queuing ch1" 
          using  a1 unfolding alpha_ArincG_def
          by auto
        then have "\<exists>ch1. chans  (communication_' \<Sigma>) ch = Some ch1 \<and> chan_queuing ch1" 
          using chans_ca port_channel_c_ca a01 by auto
      } ultimately have "\<exists>ch1. chans  (communication_' \<Sigma>) ch = Some ch1 \<and> chan_queuing ch1" 
        by fastforce
    } then have  "{ch.\<exists>ch1. chans (communication_' \<sigma>) ch = Some ch1 \<and> chan_queuing ch1} \<subseteq> 
                  {ch. \<exists>ch1. chans  (communication_' \<Sigma>) ch = Some ch1 \<and> chan_queuing ch1}"
      by auto
    moreover {fix ch
      assume a00:"\<exists>ch1. chans (communication_' \<Sigma>) ch = Some ch1 \<and> chan_queuing ch1"
      then obtain ch1 where a00:"chans (communication_' \<Sigma>) ch = Some ch1 \<and> chan_queuing ch1" 
        by auto
      {assume a01:"ch = port_channel conf c (pt (l!i))"
        then obtain ch1 where css:"chans c ch = Some ch1 \<and> chan_queuing ch1"          
          using port_open_queuing_some_chan_queuing
          by (metis a11' local.a2 p_queue vars.select_convs(1))               
        then have "\<exists>ch1. chans (communication_' \<sigma>) ch = Some ch1 \<and> chan_queuing ch1" 
          using a13 l1 port_channel_c_ca 
          unfolding port_set_mutex_def Let_def channel_set_mutex_def
            chan_queuing_def chan_sampling_def
          by auto
      }
      moreover 
      {assume a01:"ch \<noteq> port_channel conf c (pt (l!i))"
        then have "chans ca ch = Some ch1 \<and> chan_queuing ch1" 
          using a00 chans_ca port_channel_c_ca by auto
        then have "\<exists>ch1. chans c ch = Some ch1 \<and> chan_queuing ch1" 
          using  a1 unfolding alpha_ArincG_def
          by auto
        then have "\<exists>ch1. chans (communication_' \<sigma>) ch = Some ch1 \<and> chan_queuing ch1" 
          using chans_c a01 by auto
      } ultimately have "\<exists>ch1. chans  (communication_' \<sigma>) ch = Some ch1 \<and> chan_queuing ch1" 
        by fastforce
    } then have  "{ch.\<exists>ch1. chans (communication_' \<Sigma>) ch = Some ch1 \<and> chan_queuing ch1} \<subseteq> 
                  {ch. \<exists>ch1. chans  (communication_' \<sigma>) ch = Some ch1 \<and> chan_queuing ch1}"
      by auto
    ultimately show ?thesis by auto
  qed
  moreover have "(\<forall>ch_id.             
              (mut (the (chans (communication_' \<sigma>) ch_id)) = 
                mut (the (chans (communication_' \<Sigma>) ch_id))) \<and>
              ( mut (the (chans (communication_' \<Sigma>) ch_id)) = 0 \<longrightarrow>
                 data (the (chans (communication_' \<sigma>) ch_id)) =                            
                     data (the (chans (communication_' \<Sigma>) ch_id))))"
  proof-
  {fix ch_id
    have p1:"mut (the (chans (communication_' \<sigma>) ch_id)) = 
                mut (the (chans (communication_' \<Sigma>) ch_id))"
    proof-
      {assume a01:"ch_id = port_channel conf c (pt (l!i))"
        then have ?thesis
        proof -
          have "ports (communication_' \<sigma>) = ports ca"
            by (metis eq_ports_c_ca ports_c)
          then have "ports (communication_' \<sigma>) = ports (communication_' \<Sigma>)"
            by (metis ports_ca)
          then show ?thesis
            by (metis (no_types) a01 mut_ca mut_c channel_get_mutex_def 
               eq_port_channel' l mut_\<sigma> port_get_mutex_def ports_c pt pt_eq)
        qed
      }
        moreover {
          assume "ch_id \<noteq> port_channel conf c (pt (l!i))"
        then have ?thesis
          using a1 unfolding alpha_ArincG_def
          using chans_c chans_ca port_channel_c_ca by auto
      } ultimately show ?thesis by auto
    qed     
    moreover have p2:"mut (the (chans (communication_' \<Sigma>) ch_id)) = 0 \<longrightarrow>
                 data (the (chans (communication_' \<sigma>) ch_id)) = 
                     data (the (chans (communication_' \<Sigma>) ch_id))"
    proof-
      {assume a01:"ch_id = port_channel conf c (pt (l!i))"
        then have ?thesis
        proof -
          have a01':"ch_id = port_channel conf ca (pt (la!i))"
            using a01 port_channel_c_ca by auto
          have "ports (communication_' \<sigma>) = ports ca"
            by (metis eq_ports_c_ca ports_c)
          then have "ports (communication_' \<sigma>) = ports (communication_' \<Sigma>)"
            by (metis ports_ca)
          
          have ch_c:"channel_get_messages (the (chans (communication_' \<sigma>) ch_id))  = 
               channel_get_messages (the (chans c (port_channel conf c (pt (l! i)))))"
            using a13
          proof -
            have "port_channel conf (communication_' \<sigma>) (pt (l ! i)) = port_channel conf c (pt (l ! i))"
              by (metis (no_types) eq_port_channel' ports_c)
            then show ?thesis
              using c_messages a01 port_get_messages_def ptl by auto
          qed 
          moreover have ch_c:"port_get_messages conf (communication_' \<sigma>) (pt (l!i)) =
           add_mset (msg (l ! i)) (channel_get_messages (the (chans ca
                 (port_channel conf ca (pt (la ! i))))))"
            using a7 ch_c a01 unfolding port_get_messages_def Let_def
            using c_messages l port_get_messages_def by auto  
          moreover have "msg (l ! i) = msg (la ! i)" 
            using a1 unfolding alpha_ArincG_def by auto
          ultimately have "add_mset (msg (l ! i)) (channel_get_messages (the (chans ca
                 (port_channel conf ca (pt (la ! i)))))) = (port_get_messages conf ca (pt (la!i))) + {# (msg (la ! i))#}"
            unfolding port_get_messages_def Let_def by auto
          moreover have "port_get_messages conf (communication_' \<Sigma>) (pt (la ! i)) = 
               port_get_messages conf (port_insert_message conf ca (pt (la ! i)) (msg (la ! i)) 0) (pt (la ! i))"
            using   ports_ca pt  mut_ca a01' port_get_insert by auto  
          then have "port_get_messages conf (communication_' \<Sigma>) (pt (la ! i))  = 
                     (port_get_messages conf ca (pt (la!i))) + {# (msg (la ! i))#}" 
            using queuing_port_insert[OF a11] a3 a4 by auto          
          ultimately have p_m:"port_get_messages conf (communication_' \<sigma>) (pt (l!i)) = 
                     port_get_messages conf (communication_' \<Sigma>) (pt (l! i))"
            using ch_c pt_eq a01 a7 unfolding port_get_messages_def Let_def
            by auto
          have "\<exists>chan. chans (communication_' \<Sigma>) (port_channel conf ca (pt (la ! i))) = Some chan \<and>
                              chan_queuing chan"
            using eq_types chan_queuing_c port_channel_c_ca by auto
          then obtain chan where ch1:"chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (l ! i))) = Some chan \<and>
                              chan_queuing chan"
            using pt_eq port_channel_ca_\<Sigma> port_channel_c_\<sigma> by auto
          obtain chan' where ch2:"chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (l ! i))) = Some chan' \<and>
                              chan_queuing chan'"
            using chan_queuing_c port_channel_c_\<sigma> by auto
          then have "data (the (chans (communication_' \<sigma>)
                       (port_channel conf (communication_' \<sigma>) (pt (l ! i))))) =
                     data (the (chans (communication_' \<Sigma>)
                    (port_channel conf (communication_' \<Sigma>) (pt (l ! i)))))" 
            using eq_port_messages_same_data[OF p_m ch2 ch1] ch1 by auto
          then show ?thesis using eq_port_messages_same_data[OF p_m ch2 ch1] chan_queuing_c
            pt_eq a01 ptl pt port_channel_ca_\<Sigma> port_channel_c_\<sigma>
            by (simp add: port_channel_c_ca)             
        qed
      }
      moreover { 
          assume "ch_id \<noteq> port_channel conf c (pt (l!i))"
        then have ?thesis
          using a1 unfolding alpha_ArincG_def
          using chans_c chans_ca port_channel_c_ca by auto
      } ultimately show ?thesis by fastforce
    qed         
    note conjI[OF p1 p2]
  } thus ?thesis by auto
  qed
  ultimately show ?thesis unfolding alpha_ArincG_def by auto
qed

lemma sta_send2S:"Sta\<^sub>sS ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
           \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
           \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot> 
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
           ({(\<sigma>, \<Sigma>).
             a_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
             a_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
             r_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
             r_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))} \<inter>
            {(\<sigma>, \<Sigma>).
             \<exists>d. channel_get_messages
                  (the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) =
                 d + {#msg (locals_' \<sigma> ! i)#} \<and>
                 channel_get_messages
                  (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))))) =
                 d} \<inter>
            \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
            \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
           \<lbrace>True\<rbrace> \<odot>  (- \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>))
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
apply (simp) by (rule eq_sta\<^sub>s_preS[ OF sta_s_int_intro[OF sta_s_int_intro[OF 
                          sta_s_int_intro [OF 
                            sta_s_int_intro[OF sta_s_1'[simplified pre_Arinci_def pre_Arinc_def] 
                                               Sta_s_sta_intro1[OF sta_cond_imp sta_cond_spec]]
                              sta_s_aux'[simplified]] 
                Sta_s_sta_r_intro[OF Sta_port_full_spec]] sta_s_int_ex[OF Sta_channel_eq_data get_data_sta[simplified]]]];
  auto simp add: and_rel_def)

lemma "Sta\<^sub>s ({(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
           \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
           \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot> 
           (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
               p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
               \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
           ({(\<sigma>, \<Sigma>).
             a_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
             a_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
             r_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
             r_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))} \<inter>
            {(\<sigma>, \<Sigma>).
             \<exists>d. channel_get_messages
                  (the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) =
                 d + {#msg (locals_' \<sigma> ! i)#} \<and>
                 channel_get_messages
                  (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))))) =
                 d} \<inter>
            \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
            \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
           \<lbrace>True\<rbrace> \<odot>  (- \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>))
     (ArincImp.Rely_Send_ReceiveQ i, (ArincQueuing.Rely_Send_ReceiveQ i)\<^sup>*)\<^sub>\<alpha>\<^sub>A\<^sub>g"
  using sta_send2S eq_related_tran by auto
declare eq_related_tran[THEN sym,simp]

lemma sim_send2:" i < Sys_Config.procs conf \<Longrightarrow>    
   \<xi> = {(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
                  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
                  (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
                  (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
                  ({(\<sigma>, \<Sigma>).
                    a_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                    a_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))  \<and>
                    r_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                    r_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                    data (the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) = 
                    data (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter>
                   \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
                   \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
                  - \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  \<lbrace>True\<rbrace> \<Longrightarrow>
    (ArincImp.\<Gamma>,(\<acute>communication :== port_insert_message conf \<acute>communication (pt (\<acute>locals ! i)) (msg (\<acute>locals ! i)) 0;;
                  (\<acute>locals ! i :== (\<acute>locals ! i)
                  \<lparr>a_que_aux :=
                     set_que_aux conf \<acute>communication (pt (\<acute>locals ! i)) (a_que_aux (\<acute>locals ! i))
                      (add_mset (msg (\<acute>locals ! i))
                        (get_que_aux conf \<acute>communication (pt (\<acute>locals ! i)) (a_que_aux (\<acute>locals ! i))))\<rparr>;;
                  (\<acute>locals ! i :== (\<acute>locals ! i)\<lparr>ret_n := Suc 0\<rparr>;;
                  \<acute>communication :==\<^sub>E\<^sub>V
                  port_set_mutex conf \<acute>communication (pt (\<acute>locals ! i))
                   0))),ArincImp.Rely_Send_ReceiveQ i,ArincImp.Guarantee_Send_Receive i)
    \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>A\<^sub>g\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<alpha>\<^sub>A\<^sub>g\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>A\<^sub>i i\<^sub>)
    (ArincSpecQueue.\<Gamma>,Await UNIV
                        (IF\<^sub>s port_full conf \<acute>communication (pt (\<acute>locals ! i))
                         THEN \<acute>locals ! i :==\<^sub>s (\<acute>locals ! i)\<lparr>ret_n := Suc 0\<rparr>;;\<^sub>s
                           \<acute>communication :==\<^sub>s port_set_mutex conf \<acute>communication (pt (\<acute>locals ! i)) 0
                         ELSE \<acute>communication :==\<^sub>s
                              port_insert_message conf \<acute>communication (pt (\<acute>locals ! i)) (msg (\<acute>locals ! i)) 0;;\<^sub>s
                           \<acute>locals ! i :==\<^sub>s (\<acute>locals ! i)
                           \<lparr>a_que_aux :=
                              set_que_aux conf \<acute>communication (pt (\<acute>locals ! i)) (a_que_aux (\<acute>locals ! i))
                               (add_mset (msg (\<acute>locals ! i))
                                 (get_que_aux conf \<acute>communication (pt (\<acute>locals ! i)) (a_que_aux (\<acute>locals ! i))))\<rparr>;;\<^sub>s
                           \<acute>communication :==\<^sub>s port_set_mutex conf \<acute>communication (pt (\<acute>locals ! i)) 0;;\<^sub>s
                           \<acute>locals ! i :==\<^sub>s (\<acute>locals ! i)\<lparr>ret_n := Suc 0\<rparr>
                         FI)
                        (Some E\<^sub>V),ArincQueuing.Rely_Send_ReceiveQ i,ArincQueuing.Guarantee_Send_Receive i)" 
apply (rule imp_seq_Basic_Spec_sim[where \<xi>\<^sub>1 = "{(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
                  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
                  (\<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
                  (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
                  ({(\<sigma>, \<Sigma>).
                    a_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                    a_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))  \<and>
                    r_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                    r_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))} \<inter>
                    {(\<sigma>,\<Sigma>). (\<exists>d. (channel_get_messages (the (chans (communication_' \<sigma>)(port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i)))))) = 
                        d + {# (msg (locals_' \<sigma> ! i)) #} \<and> 
                        (channel_get_messages (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))) = d )} \<inter>
                   \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
                   \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
                  \<lbrace>True\<rbrace> \<odot>  (-\<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)"  ])
            apply auto[2]     
        apply (fastforce intro: sta_cond_not_full) 
apply (simp) apply (rule eq_sta\<^sub>s_preS[ OF sta_s_int_intro[OF sta_s_int_intro[OF 
                          sta_s_int_intro [OF 
                            sta_s_int_intro[OF sta_s_1'[simplified pre_Arinci_def pre_Arinc_def] 
                                               Sta_s_sta_intro1[OF sta_cond_imp sta_cond_spec]]
                              sta_s_aux'[simplified]] 
                Sta_s_sta_r_intro[OF Sta_port_full_spec]] sta_s_int_ex[OF Sta_channel_eq_data get_data_sta[simplified]]]];
  auto simp add: and_rel_def)
         apply (auto simp add:  imp_guarante_ref reflexive_Guarantee_Send 
                 Rely_Send_ReceiveQ_def ArincQueuing.Rely_Send_ReceiveQ_def alpha_xstate'_def)[3] 
   apply (insert sim2_seq1_post; auto)
apply (rule imp_seq_Basic_Spec_sim[where \<xi>\<^sub>1 = "{(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
                  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
                  (\<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
                  (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
                   {(\<sigma>, \<Sigma>).                    
                    r_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                    r_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))} \<inter>
                   {(\<sigma>, \<Sigma>). 
                      (\<exists>a.  a_que_aux (locals_' \<Sigma> ! i) 
                             (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) = a \<and>
                            a_que_aux (locals_' \<sigma> ! i) 
                              (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = a + {# (msg (locals_' \<sigma> ! i)) #})} \<inter>
                    {(\<sigma>,\<Sigma>). (\<exists>d. (channel_get_messages (the (chans (communication_' \<sigma>)(port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i)))))) = 
                        d + {# (msg (locals_' \<sigma> ! i)) #} \<and> 
                        (channel_get_messages (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))) = d )} \<inter>
                   \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
                   \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter>
                  \<lbrace>True\<rbrace> \<odot>  (-\<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)"  ])
            apply auto[2]     
 apply (simp) apply(rule eq_sta\<^sub>s_preS[ OF sta_s_int_intro[OF sta_s_int_intro[OF 
                          sta_s_int_intro [OF 
                            sta_s_int_intro[OF sta_s_1'[simplified pre_Arinci_def pre_Arinc_def] 
                                               Sta_s_sta_intro1[OF sta_cond_imp sta_cond_spec]]
                              sta_s_aux[simplified]] 
                Sta_s_sta_r_intro[OF Sta_port_full_spec]] sta_s_int_ex[OF Sta_channel_eq_data get_data_sta[simplified]]]];
  auto simp add: and_rel_def)          
apply (simp, rule eq_sta\<^sub>s_preS[ OF sta_s_int_intro[OF sta_s_int_intro[OF
                          sta_s_int_intro [OF 
                            sta_s_int_intro[OF sta_s_1'[simplified pre_Arinci_def pre_Arinc_def] 
                                               Sta_s_sta_intro1[OF sta_cond_imp sta_cond_spec]]
                              sta_s_r_aux[simplified]] 
                Sta_s_sta_r_intro[OF Sta_port_full_spec]] sta_s_int_intro[OF  
        sta_s_int_ex[OF Sta_aux_a_imp Sta_aux_a_spec[simplified]]
         sta_s_int_ex[OF Sta_channel_eq_data get_data_sta[simplified]]]]];
  auto simp add: and_rel_def)
        apply (auto simp add:  imp_guarante_ref reflexive_Guarantee_Send 
                 Rely_Send_ReceiveQ_def ArincQueuing.Rely_Send_ReceiveQ_def alpha_xstate'_def)[3]
   apply (insert sim2_seq2_post; auto)
apply (rule imp_seq_Basic_Spec_sim[where \<xi>\<^sub>1 = "{(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
                  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
                  (\<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
                  (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
                   {(\<sigma>, \<Sigma>).                    
                    r_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                    r_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))} \<inter>
                   {(\<sigma>, \<Sigma>). 
                      (\<exists>a.  a_que_aux (locals_' \<Sigma> ! i) 
                             (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) = a \<and>
                            a_que_aux (locals_' \<sigma> ! i) 
                              (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = a + {# (msg (locals_' \<sigma> ! i)) #})} \<inter>
                    {(\<sigma>,\<Sigma>). (\<exists>d. (channel_get_messages (the (chans (communication_' \<sigma>)(port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i)))))) = 
                        d + {# (msg (locals_' \<sigma> ! i)) #} \<and> 
                        (channel_get_messages (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))) = d )} \<inter>
                   \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
                   \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter>
                  \<lbrace>True\<rbrace> \<odot>  (-\<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)\<inter>
                  \<lbrace>ret_n (\<acute>locals ! i) = Suc 0\<rbrace> \<odot>  \<lbrace>True\<rbrace>"  ])
  apply auto[2]
apply (simp, rule eq_sta\<^sub>s_preS[ OF sta_s_int_intro[OF sta_s_int_intro[OF
                          sta_s_int_intro [OF 
                            sta_s_int_intro[OF sta_s_1'[simplified pre_Arinci_def pre_Arinc_def] 
                                               Sta_s_sta_intro1[OF sta_cond_imp sta_cond_spec]]
                              sta_s_r_aux[simplified]] 
                Sta_s_sta_r_intro[OF Sta_port_full_spec]] sta_s_int_intro[OF  
        sta_s_int_ex[OF Sta_aux_a_imp Sta_aux_a_spec[simplified]]
         sta_s_int_ex[OF Sta_channel_eq_data get_data_sta[simplified]]]]];
  auto simp add: and_rel_def)

 apply (simp, rule eq_sta\<^sub>s_preS[ OF sta_s_int_intro[OF Sta_s_sta_l_intro[OF Sta_imp_ret_n]
                         sta_s_int_intro[OF sta_s_int_intro[OF
                          sta_s_int_intro [OF 
                            sta_s_int_intro[OF sta_s_1'[simplified pre_Arinci_def pre_Arinc_def] 
                                               Sta_s_sta_intro1[OF sta_cond_imp sta_cond_spec]]
                              sta_s_r_aux[simplified]] 
                Sta_s_sta_r_intro[OF Sta_port_full_spec]] sta_s_int_intro[OF  
        sta_s_int_ex[OF Sta_aux_a_imp Sta_aux_a_spec[simplified]]
         sta_s_int_ex[OF Sta_channel_eq_data get_data_sta[simplified]]]]]];
  auto simp add: and_rel_def)
  apply (auto simp add:  imp_guarante_ref reflexive_Guarantee_Send 
                 Rely_Send_ReceiveQ_def ArincQueuing.Rely_Send_ReceiveQ_def alpha_xstate'_def)[3]
   apply (insert sim2_seq3_post; auto)
  apply (rule mod_state_Await_Spec_Sim[where F="{}"])
                 apply (auto simp add: posta_Arinci_def)[3]
apply (simp, rule eq_sta\<^sub>s_preS[ OF sta_s_int_intro[OF Sta_s_sta_l_intro[OF Sta_imp_ret_n]
                         sta_s_int_intro[OF sta_s_int_intro[OF
                          sta_s_int_intro [OF 
                            sta_s_int_intro[OF sta_s_1'[simplified pre_Arinci_def pre_Arinc_def] 
                                               Sta_s_sta_intro1[OF sta_cond_imp sta_cond_spec]]
                              sta_s_r_aux[simplified]] 
                Sta_s_sta_r_intro[OF Sta_port_full_spec]] sta_s_int_intro[OF  
        sta_s_int_ex[OF Sta_aux_a_imp Sta_aux_a_spec[simplified]]
         sta_s_int_ex[OF Sta_channel_eq_data get_data_sta[simplified]]]]]];
  auto simp add: and_rel_def) 
             apply (fastforce intro: stable_related')
            apply (fastforce simp:posta_Arinci_def intro: stable_related')
           apply (simp add: imp_guarante_ref)
          apply (auto simp add: ArincImp.Rely_Send_ReceiveQ_def alpha_xstate'_def ArincQueuing.Rely_Send_ReceiveQ_def)[3]
  apply (auto simp add: and_rel_def, drule p_q ,simp)[1]
  apply (auto simp add:  ArincImp.Guarantee_Send_Receive_def Let_def Guarantee_mod_chan_def Guarantee_Send_Receive'_def
port_set_mutex_def channel_set_mutex_def state_conf_def chan_queuing_def chan_sampling_def port_exists_def
port_channel_def port_in_channel_def port_id_name_def and_rel_def port_open_def port_id_in_part_def
 current_def  p_queuing_def ch_id_queuing_def port_get_mutex_def channel_get_mutex_def
 channel_get_messages_def)[1]
  apply auto
  apply vcg
  apply (drule a2_inv, simp)
apply (auto simp add: eq_insert) 
        apply (auto simp add: and_rel_def port_full_def channel_full_def Let_def channel_get_bufsize_def channel_get_messages_def
alpha_ArincG_def port_channel_def port_in_channel_def port_id_name_def port_exists_def)[2]
   apply (simp_all add: and_rel_def)
   apply (simp add: guarantee_send_message)
  by (auto simp add: rel_send_message)

   
      
lemma sim_send:
 " i < Sys_Config.procs conf \<Longrightarrow>
    \<xi>\<^sub>A\<^sub>1 = \<xi>\<^sub>A\<^sub>i B adds rems i \<Longrightarrow>
    \<gamma>\<^sub>n\<^sub>A\<^sub>1 = \<gamma>\<^sub>n\<^sub>A\<^sub>i i \<Longrightarrow>
    \<gamma>\<^sub>a\<^sub>A\<^sub>1 = \<gamma>\<^sub>a\<^sub>A\<^sub>i i \<Longrightarrow>
    p\<^sub>r\<^sub>e =
    \<xi>\<^sub>A\<^sub>i B adds rems i \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
    \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<Longrightarrow>        
       (ArincImp.\<Gamma>,send_q_message_i i,ArincImp.Rely_Send_ReceiveQ i,ArincImp.Guarantee_Send_Receive i)
       \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>A\<^sub>g\<^sub>;\<^sub>p\<^sub>r\<^sub>e\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>A\<^sub>i i\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>A\<^sub>i i\<^sub>)
       (ArincSpecQueue.\<Gamma>,ArincSpec_com_queue_insert.send_q_message_i i,ArincQueuing.Rely_Send_ReceiveQ
                               i,ArincQueuing.Guarantee_Send_Receive i)"
  unfolding send_q_message_i_def ArincSpec_com_queue_insert.send_q_message_i_def
 apply (rule If_sound)
           apply (auto simp add: pre_Arinci_def pre_Arinc_def postn_Arinci_def)[1]
          apply (simp add: sta_s_1')
      apply (simp add: imp_guarante_ref)
   apply (auto simp add: ArincImp.Rely_Send_ReceiveQ_def pre_Arinci_def pre_Arinc_def
         ArincQueuing.Rely_Send_ReceiveQ_def alpha_xstate'_def  
        ArincImp.\<Gamma>_def ArincSpecQueue.\<Gamma>_def f_equiv_def)[4]  
    apply (simp add: current_def pre_Arinci_def pre_Arinc_def eq_rel_def and_rel_def alpha_ArincG_def 
          p_queuing_def port_channel_def port_in_channel_def port_id_name_def 
          p_source_def port_id_in_part_def  port_exists_def port_open_def port_max_size_def )  
   apply (rule mod_state_tau_sound)
              apply (auto simp add: pre_Arinci_def pre_Arinc_def postn_Arinci_def posta_Arinci_def)[3]
           apply (fastforce intro: sta_s_2)
  unfolding postn_Arinci_def
          apply (simp add: stable_related' postn_Arinci_def posta_Arinci_def)+
  using imp_guarante_ref 
        apply auto[1]
       apply (auto simp add:  ArincImp.Rely_Send_ReceiveQ_def ArincQueuing.Rely_Send_ReceiveQ_def 
                              alpha_xstate'_def )[3]
   apply (clarify)
   apply (drule basic_ret_0_sim, assumption+, simp+, (simp add: state_conf_def), (simp add: state_conf_def))
  apply (rule Seq_sound[where \<gamma>\<^sub>r = "{(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter>                   
                  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot>  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
                  (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
                  (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      \<not> snd (msg (\<acute>locals ! i))
                         \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>               
              ({(\<sigma>, \<Sigma>). a_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = a_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                           r_que_aux ((locals_' \<sigma>)!i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = r_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                        data (the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) = 
                           data (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter> 
              \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = (Suc i)\<rbrace> \<odot>
              \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = (Suc i)\<rbrace>)"])
apply (auto simp add:  ArincImp.Rely_Send_ReceiveQ_def ArincQueuing.Rely_Send_ReceiveQ_def 
                              alpha_xstate'_def posta_Arinci_def sta_s_3)[1]
        apply (fast intro: sta_s_3)
       apply (auto simp add: posta_Arinci_def stable_related')[1]  
      apply (auto simp add:  ArincImp.Rely_Send_ReceiveQ_def ArincQueuing.Rely_Send_ReceiveQ_def 
                              alpha_xstate'_def posta_Arinci_def imp_guarante_ref)[2]
   apply (rule mod_state_Await_sound[where F="{}"])
                   apply (auto simp add:  ArincImp.Rely_Send_ReceiveQ_def ArincQueuing.Rely_Send_ReceiveQ_def 
                              alpha_xstate_def posta_Arinci_def sta_s_3 imp_guarante_ref )[3]
                apply (fastforce intro: sta_s_3)
               apply (fast intro: sta_s_6)  
              apply (simp add:posta_Arinci_def stable_related')
             apply (auto simp add: imp_guarante_ref ArincQueuing.Rely_Send_ReceiveQ_def 
                    ArincImp.Rely_Send_ReceiveQ_def alpha_xstate'_def)[4]
        apply auto
      apply (simp add:  sat_await_body_mut)   
  apply (vcg, blast dest:  sim_await_set_mut_normal)  
    apply (blast dest: hoare_not_in_s[OF _ _ no_abrupt[of True], of i _ _ False])
  apply (auto simp add: eq_rel_def port_get_mutex_def Let_def channel_get_mutex_def port_channel_def
   port_in_channel_def port_id_name_def port_exists_def alpha_ArincG_def)[1]   
  apply (rule If_branch_imp_sound)
          apply (auto simp add: pre_Arinci_def pre_Arinc_def postn_Arinci_def)[1]
         apply (fast intro: sta_s_6)  
        apply (simp add: imp_guarante_ref)
       apply (auto simp add:  ArincImp.Rely_Send_ReceiveQ_def ArincQueuing.Rely_Send_ReceiveQ_def 
                              alpha_xstate'_def posta_Arinci_def imp_guarante_ref)[3]    
  apply (force simp add: posta_Arinci_def dest: sim_send1[of i "{(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
                  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
                  (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
                  (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
                  ({(\<sigma>, \<Sigma>).
                    a_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                    a_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                    r_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                    r_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                    data (the (chans (communication_' \<sigma>)
                                (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) =
                    data (the (chans (communication_' \<Sigma>)
                                (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter>
                   \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
                   \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
                  \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  UNIV"])
  by (force dest:  sim_send2[of i "{(\<sigma>, \<Sigma>). (\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g \<and> state_conf \<sigma>} \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
                  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<inter>
                  (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<odot> 
                  (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                      \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>) \<inter>
                  ({(\<sigma>, \<Sigma>).
                    a_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                    a_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                    r_que_aux (locals_' \<sigma> ! i) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) =
                    r_que_aux (locals_' \<Sigma> ! i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) \<and>
                    data (the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) =
                    data (the (chans (communication_' \<Sigma>) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i)))))} \<inter>
                   \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<odot> 
                   \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>) \<inter>
                  - \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<odot>  \<lbrace>True\<rbrace>"])
  
 
lemma sim_call:"i < Sys_Config.procs conf \<Longrightarrow>
    \<xi>\<^sub>A\<^sub>1 = \<xi>\<^sub>A\<^sub>i B adds rems i \<Longrightarrow>
    \<gamma>\<^sub>n\<^sub>A\<^sub>1 = \<gamma>\<^sub>n\<^sub>A\<^sub>i i \<Longrightarrow>
    \<gamma>\<^sub>a\<^sub>A\<^sub>1 = \<gamma>\<^sub>a\<^sub>A\<^sub>i i \<Longrightarrow>
    p\<^sub>r\<^sub>e = \<xi>\<^sub>A\<^sub>i B adds rems i \<inter> \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<odot> 
                  \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace> \<Longrightarrow>
    (ArincImp.\<Gamma>,LanguageCon.com.Call
                  (Send_Message_Q, i),ArincImp.Rely_Send_ReceiveQ i,ArincImp.Guarantee_Send_Receive i)
    \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>A\<^sub>g\<^sub>;\<^sub>p\<^sub>r\<^sub>e\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>A\<^sub>i i\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>A\<^sub>i i\<^sub>)
    (ArincSpecQueue.\<Gamma>,LanguageCon.com.Call
                        (Send_Message_Q,
                         i),ArincQueuing.Rely_Send_ReceiveQ i,ArincQueuing.Guarantee_Send_Receive i)"
  apply (rule Call_sound)
        apply (auto simp add: pre_Arinci_def pre_Arinc_def postn_Arinci_def)[1]
       apply (auto simp add: sta_s_1')[1]
      apply (simp add: imp_guarante_ref)
  apply (auto simp add: ArincImp.Rely_Send_ReceiveQ_def
         ArincQueuing.Rely_Send_ReceiveQ_def alpha_xstate'_def  ArincImp.\<Gamma>_def ArincSpecQueue.\<Gamma>_def f_equiv_def)[3]
  by (auto simp add: sim_send ArincImp.body_send ArincSpecQueue.body_send)

lemma imp_rely_x:"(a, b) \<in> ArincImp.Rely_Send_ReceiveQ i \<Longrightarrow> (a, b) \<in> \<alpha>\<^sub>x"
  unfolding ArincImp.Rely_Send_ReceiveQ_def alpha_xstate_def by auto

lemma spec_rely_x:"(a, b) \<in> ArincQueuing.Rely_Send_ReceiveQ i \<Longrightarrow> (a, b) \<in> \<alpha>\<^sub>x"
  unfolding ArincQueuing.Rely_Send_ReceiveQ_def alpha_xstate_def by auto
 
lemma sim_skip_1:"     
    (ArincImp.\<Gamma>,SKIP,ArincImp.Rely_Send_ReceiveQ i,ArincImp.Guarantee_Send_Receive i)
    \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>A\<^sub>g\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>A\<^sub>i i\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>A\<^sub>i i\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>A\<^sub>i i\<^sub>)
    (ArincSpecQueue.\<Gamma>,SKIP,ArincQueuing.Rely_Send_ReceiveQ i,ArincQueuing.Guarantee_Send_Receive i)"
  apply (rule Skip_sound)
     apply (auto simp add: postn_Arinci_def imp_rely_x spec_rely_x imp_guarante_ref stable_related')
  by (auto simp add: alpha_xstate'_def ArincImp.Rely_Send_ReceiveQ_def)

lemma sim_skip:" i < Sys_Config.procs conf \<Longrightarrow>    
    \<gamma>\<^sub>n\<^sub>A\<^sub>1 = \<gamma>\<^sub>n\<^sub>A\<^sub>i i \<Longrightarrow>
    \<gamma>\<^sub>a\<^sub>A\<^sub>1 = \<gamma>\<^sub>a\<^sub>A\<^sub>i i \<Longrightarrow>
    p\<^sub>r\<^sub>e = \<xi>\<^sub>A\<^sub>i B adds rems i \<inter> (- \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace>) \<odot> 
                  (- \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace>) \<Longrightarrow>
    (ArincImp.\<Gamma>,SKIP,ArincImp.Rely_Send_ReceiveQ i,ArincImp.Guarantee_Send_Receive i)
    \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>A\<^sub>g\<^sub>;\<^sub>p\<^sub>r\<^sub>e \<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>A\<^sub>i i\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>A\<^sub>i i\<^sub>)
    (ArincSpecQueue.\<Gamma>,SKIP,ArincQueuing.Rely_Send_ReceiveQ i,ArincQueuing.Guarantee_Send_Receive i)"
  apply (rule RGSim_Conseq[OF _ _ _ _  _ _ _ _ _ sim_skip_1[of i]]) 
  by (auto simp add:  postn_Arinci_def pre_Arinci_def pre_Arinc_def posta_Arinci_def ArincImp.Rely_Send_ReceiveQ_def
                 ArincQueuing.Rely_Send_ReceiveQ_def alpha_xstate'_def imp_guarante_ref)
   
lemma sim:
  "i < procs conf \<Longrightarrow> \<xi>\<^sub>A\<^sub>1 = \<xi>\<^sub>A\<^sub>i B adds rems i \<Longrightarrow> \<gamma>\<^sub>n\<^sub>A\<^sub>1 = \<gamma>\<^sub>n\<^sub>A\<^sub>i i \<Longrightarrow> \<gamma>\<^sub>a\<^sub>A\<^sub>1 = \<gamma>\<^sub>a\<^sub>A\<^sub>i i \<Longrightarrow>
     (ArincImp.\<Gamma>,ArincImp.execute_service i,Rely_Send_ReceiveQ i,Guarantee_Send_Receive i) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>A\<^sub>g\<^sub>;\<^sub>\<xi>\<^sub>A\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>A\<^sub>1\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>A\<^sub>1\<^sub>) 
     (ArincSpecQueue.\<Gamma>,ArincSpecQueue.execute_service i,ArincQueuing.Rely_Send_ReceiveQ i,ArincQueuing.Guarantee_Send_Receive i)"
  unfolding ArincImp.execute_service_def ArincSpecQueue.execute_service_def
  apply simp
  apply (rule If_sound)
           apply (simp add: alpha_ArincG_def pre_Arinci_def pre_Arinc_def postn_Arinci_def  alpha_xstate'_def,force)             
          apply (auto simp add:  sta_s' imp_guarante_ref)          
     apply (auto simp add:  ArincImp.Rely_Send_ReceiveQ_def alpha_xstate'_def ArincQueuing.Rely_Send_ReceiveQ_def)[2]
    apply (auto simp add: pre_Arinci_def pre_Arinc_def   
                          eq_rel_def ToNorm_def alpha_ArincG_def Invariant_def  dest:i_lenght)[1]           
  by (auto simp add: sim_call sim_skip)

lemma SIM:" \<xi>\<^sub>A\<^sub>1 = \<xi>\<^sub>A B adds rems \<Longrightarrow> 
          (ArincImp.\<Gamma>,PCom\<^sub>c (sim_prog B adds rems),CRef.Id,{(x,y). True}) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>A\<^sub>g\<^sub>;\<^sub>\<xi>\<^sub>A\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>A\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>A\<^sub>) 
          (ArincSpecQueue.\<Gamma>,PCom\<^sub>s (sim_prog B adds rems), CRef.Id,{(x,y). True})"
  apply (rule sim_comp)
               apply (simp add: n_n sim_prog_def)
              apply (auto simp add:  sim_prog_def Id_def Com\<^sub>c_def  Rel\<^sub>c_def Gua\<^sub>c_def Com\<^sub>s_def  Rel\<^sub>s_def Gua\<^sub>s_def Pre_def PostQ_def PostA_def)
                 apply(simp add: pre_Arinc_def alpha_ArincG_def ArincImp.Rely_Send_ReceiveQ_def)
                apply(simp add: guar_in_rely)
               apply(simp add: pre_Arinc_def alpha_ArincG_def ArincQueuing.Rely_Send_ReceiveQ_def)
              apply (simp add: Guar_Rely_Send_ReceiveQ)  
           apply (simp add:pre_Arinc_def pre_Arinci_def)    
          apply (simp add: postn_Arinci_def postn_Arinc_def, metis n_n)    
         apply (simp add:sim postn_Arinc_def posta_Arinc_def posta_Arinci_def )+         
     apply (auto simp add:    alpha_ArincG_def Rely_def alpha_xstate'_def ArincImp.Rely_Send_ReceiveQ_def ArincQueuing.Rely_Send_ReceiveQ_def)[1]    
   apply (auto simp add: postn_Arinci_def posta_Arinci_def stable_related')    
  by (simp add: imp_guarante_ref)    
    

section {* Proof of compositionality of the simulation*}

lemma validityI:"ArincSpecQueue.\<Gamma>,{} \<Turnstile>\<^bsub>/{}\<^esub> (spec_program B adds rems) 
   SAT[Inv_QueCom_mut  B adds rems \<inter>  
      {s. \<forall>ch_id. \<forall>ch. (chans (communication_' s) ch_id = Some ch \<longrightarrow> mut ch = 0)}, 
      Relation.Id, {(x,y). True}, Inv_QueCom_mut B adds rems, \<lbrace> True \<rbrace>]"
  using ArincSpecQueue.Send_Receive_Correct_mut par_rgsound unfolding spec_program_def   
  by blast
    
   
lemma Pre_arinc_Domain:"Inv_QueCom_mut  B adds rems \<inter>  
      {s. \<forall>ch_id. \<forall>ch. (chans (communication_' s) ch_id = Some ch \<longrightarrow> mut ch = 0)} \<subseteq> (Domain ((\<xi>\<^sub>A B adds rems)))"      
  unfolding  Invariant_def pre_Arinc_def ToNorm_def
  using alpha_simmetric unfolding Inv_QueCom_mut_def state_conf_def by auto
    
  
lemma a1_inv:
  assumes a0:"(\<sigma>, \<Sigma>) \<in> \<alpha>\<^sub>A\<^sub>g" and 
          a1:"channel_spec_mut B adds rems ch_id \<sigma>" and 
          a2:"state_conf \<sigma>"
        shows "channel_spec_mut B adds rems ch_id \<Sigma>"      
proof-
have eq_len:"length (locals_' \<sigma>) = length (locals_' \<Sigma>)"  
    using a0 unfolding alpha_ArincG_def by auto 
  {fix ch
   assume a00:"(chans (communication_' \<Sigma>) ch_id) = Some ch" and 
          a01:"ch_id_queuing conf ch_id" and 
          a02:"channel_get_mutex ch = 0"     

   then have eq_mut:"                
                (mut (the (chans (communication_' \<sigma>) ch_id)) = 
                mut (the (chans (communication_' \<Sigma>) ch_id))) \<and>
              ((\<exists>ch. (chans (communication_' \<sigma>) ch_id) = Some ch) \<and>
                mut (the (chans (communication_' \<Sigma>) ch_id)) = 0 \<longrightarrow>
                 data (the (chans (communication_' \<sigma>) ch_id)) =                            
                     data (the (chans (communication_' \<Sigma>) ch_id)))"
     using a0 unfolding alpha_ArincG_def by blast
   moreover obtain chs where s20:"(chans (communication_' \<sigma>) ch_id) = Some chs \<and> 
          ch_id_queuing conf ch_id \<and>
          mut chs = 0"
     using  a00 a01 a2 a0 a02 calculation
     unfolding alpha_ArincG_def ch_id_queuing_def state_conf_def channel_get_mutex_def by fastforce     
   then have eq_data:"data (the (chans (communication_' \<sigma>) ch_id)) =                            
                     data (the (chans (communication_' \<Sigma>) ch_id))"  
     using eq_mut a00 a02 channel_get_mutex_def by auto     
   then have eq_aux1:"\<forall>i<length (locals_' \<Sigma>). 
            a_que_aux ((locals_' \<sigma>)!i) ch_id = a_que_aux ((locals_' \<Sigma>)!i) ch_id \<and>
            r_que_aux ((locals_' \<sigma>)!i) ch_id = r_que_aux ((locals_' \<Sigma>)!i) ch_id"
     using eq_len eq_aux[OF a0] s20 unfolding channel_get_mutex_def by auto
       
  then have eq_aux: "channel_sent_messages  ch_id  adds (locals_' \<sigma>) = channel_sent_messages  ch_id  adds (locals_' \<Sigma>) \<and>
             channel_received_messages  ch_id  rems (locals_' \<sigma>) = channel_received_messages  ch_id rems (locals_' \<Sigma>)"
    using same_channel_messages[OF _ eq_len] a0
    unfolding alpha_ArincG_def channel_sent_messages_def channel_received_messages_def by auto
   have "channel_get_messages ch = 
          (B ch_id + channel_sent_messages  ch_id adds  (locals_' \<Sigma>)) -
               channel_received_messages  ch_id  rems (locals_' \<Sigma>) \<and>
         channel_received_messages  ch_id rems (locals_' \<Sigma>)  \<subseteq>#
           (B ch_id + channel_sent_messages ch_id adds (locals_' \<Sigma>)) \<and>
        (size (channel_get_messages ch) \<le> 
           channel_size (get_channel conf ch_id)) \<and>          
         channel_messages ch_id rems [0..<length (locals_' \<Sigma>)] \<subseteq># 
           channel_messages  ch_id r_que_aux (locals_' \<Sigma>) \<and>
         channel_messages ch_id adds [0..<length (locals_' \<Sigma>)] \<subseteq># 
           channel_messages  ch_id a_que_aux (locals_' \<Sigma>)"
     using eq_aux s20 eq_data channel_spec_mut_dest2[OF a1 s20]  same_channel_messages[OF _ eq_len]
          eq_aux1 a00
     unfolding  ch_spec_def channel_get_messages_def
     using eq_len by force
    } thus ?thesis unfolding channel_spec_mut_def channel_get_mutex_def ch_spec_def
      by fastforce 
qed
  
    
lemma rel_chans_inv:
assumes a0:" ch \<in> channels_conf (commconf conf)" and
        a1:"\<forall>ch\<in>channels_conf (commconf conf).
             \<exists>ch_s. chans (communication_' \<sigma>) (channel_id ch) = Some ch_s \<and> channel_queuing ch = chan_queuing ch_s" and
        a2:"{ch. \<exists>ch1. chans (communication_' \<sigma>) ch = Some ch1 \<and> chan_queuing ch1} =
          {ch. \<exists>ch1. chans (communication_' \<Sigma>) ch = Some ch1 \<and> chan_queuing ch1}" and
        a3:"{ch. chans (communication_' \<sigma>) ch = \<tau>} = {ch. chans (communication_' \<Sigma>) ch = \<tau>}" 
      shows "\<exists>ch_s. chans (communication_' \<Sigma>) (channel_id ch) = Some ch_s \<and> channel_queuing ch = chan_queuing ch_s "  
  using a0 a1 a2 a3
  using option.sel by force
    


lemma eq_mut:"\<forall>ch_id.             
              (mut (the (chans (communication_' s1) ch_id)) = 
                mut (the (chans (communication_' x) ch_id))) \<Longrightarrow> 
     \<forall>ch_id ch. chans (communication_' s1) ch_id = Some ch \<longrightarrow> mut ch = 0 \<Longrightarrow>
     chans (communication_' x) ch_id = Some ch  \<Longrightarrow> 
     {ch. chans (communication_' s1) ch = None} = 
             {ch. chans (communication_' x) ch = None} \<Longrightarrow>
      mut ch = 0"
proof -
assume a1: "\<forall>ch_id ch. chans (communication_' s1) ch_id = Some ch \<longrightarrow> mut ch = 0"
  assume a2: "\<forall>ch_id. mut (the (chans (communication_' s1) ch_id)) = mut (the (chans (communication_' x) ch_id))"
  assume a3: "{ch. chans (communication_' s1) ch = \<tau>} = {ch. chans (communication_' x) ch = \<tau>}"
  assume a4: "chans (communication_' x) ch_id = Some ch"
  have "\<forall>n. chans (communication_' x) n = \<tau> \<or> chans (communication_' s1) n \<noteq> \<tau>"
    using a3 by force
  then show ?thesis
    using a4 a2 a1 by (metis option.exhaust_sel option.sel)
qed
  

lemma Image_domain_pre_arinc:
    "Inv_QueCom_mut  B adds rems \<inter>  
     {s. \<forall>ch_id. \<forall>ch. (chans (communication_' s) ch_id = Some ch \<longrightarrow> mut ch = 0)} = 
    ((\<xi>\<^sub>A B adds rems)) `` (Inv_QueCom_mut  B adds rems \<inter>  
      {s. \<forall>ch_id. \<forall>ch. (chans (communication_' s) ch_id = Some ch \<longrightarrow> mut ch = 0)})"      
  unfolding   pre_Arinc_def ToNorm_def     
   apply (auto simp add: a1_inv a2_inv Inv_QueCom_mut_def alpha_simmetric)   
  by (auto intro: eq_mut simp add:  alpha_ArincG_def state_conf_def)

  
                        
lemma Postn_domain:"  Inv_QueCom_mut B adds rems \<subseteq> Domain (\<Down>\<^sub>i \<gamma>\<^sub>n\<^sub>A)"
  unfolding postn_Arinc_def ToInv_def alpha_ArincG_def by auto
  
    
lemma Image_domain_postn_arinc:" Inv_QueCom_mut B adds rems = (\<Down>\<^sub>i \<gamma>\<^sub>n\<^sub>A) ``  Inv_QueCom_mut B adds rems"
  unfolding  Inv_QueCom_mut_def  postn_Arinc_def  ToInv_def  
  apply (auto intro: a1 a2)
  using a3 alpha_simmetric by blast

    
lemma Posta_domain:"\<lbrace> True \<rbrace>  \<subseteq> Domain (\<Down>\<^sub>i \<gamma>\<^sub>a\<^sub>A)"
  unfolding posta_Arinc_def ToInv_def alpha_ArincG_def by auto
    
lemma Image_domain_posta_arinc:"\<lbrace> True \<rbrace> = (\<Down>\<^sub>i \<gamma>\<^sub>a\<^sub>A) `` \<lbrace> True \<rbrace>  "
  unfolding posta_Arinc_def ToInv_def alpha_ArincG_def by auto
  
lemma alpha_a_x:"\<Down>\<^sub>x \<alpha>\<^sub>A\<^sub>g \<subseteq> \<alpha>\<^sub>x" 
  unfolding ToExSt_def alpha_xstate_def alpha_ArincG_def by auto



lemma SIMi:" \<xi>\<^sub>A\<^sub>1 = \<xi>\<^sub>A B adds rems \<Longrightarrow> (ArincImp.\<Gamma>,imp_program B adds rems,CRef.Id,{(x,y). True}) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>A\<^sub>g\<^sub>;\<^sub>\<xi>\<^sub>A\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>A\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>A\<^sub>) 
                           (ArincSpecQueue.\<Gamma>,spec_program B adds rems, CRef.Id,{(x,y). True})"
  using SIM imp_program_list spec_program_list by auto    


lemma ref1: "\<xi>\<^sub>A\<^sub>1 = \<xi>\<^sub>A B  adds rems \<Longrightarrow> ArincSpecQueue.\<Gamma>\<Turnstile>\<^bsub>/{}\<^esub> spec_program B adds rems SAT[Inv_QueCom_mut  B adds rems \<inter>  
            {s. \<forall>ch_id. \<forall>ch. (chans (communication_' s) ch_id = Some ch \<longrightarrow> mut ch = 0)}, Relation.Id, {(x,y). True}, Inv_QueCom_mut B adds rems, \<lbrace> True \<rbrace>] \<longrightarrow> 
       ArincImp.\<Gamma>\<Turnstile>\<^bsub>/{}\<^esub> imp_program B adds rems SAT[Inv_QueCom_mut  B adds rems \<inter>  
            {s. \<forall>ch_id. \<forall>ch. (chans (communication_' s) ch_id = Some ch \<longrightarrow> mut ch = 0)}, Relation.Id, {(x,y). True},Inv_QueCom_mut B adds rems, \<lbrace> True \<rbrace>]"    
  unfolding  eq_id                      
                
  apply (rule RG_SIM_RG_pre[OF  SIMi, of \<xi>\<^sub>A\<^sub>1 B adds rems], assumption)
  using Pre_arinc_Domain Image_domain_pre_arinc Postn_domain 
       Image_domain_postn_arinc Posta_domain Image_domain_posta_arinc validityI  
  unfolding  eq_id  normal_relation_id_def alpha_xstate_def Id_def in_rel_def
  apply auto
  by blast+

definition Inv where
"Inv  B adds rems \<equiv> {s. state_conf s}   \<inter> {s. \<forall>ch_id. channel_spec_mut B adds rems ch_id s} \<inter>  
            {s. \<forall>ch_id. \<forall>ch. (chans (communication_' s) ch_id = Some ch \<longrightarrow> mut ch = 0)}"

lemma ref:
      "ArincImp.\<Gamma>\<Turnstile>\<^bsub>/{}\<^esub> imp_program B adds rems SAT[Inv_QueCom_mut  B adds rems \<inter>  
            {s. \<forall>ch_id. \<forall>ch. (chans (communication_' s) ch_id = Some ch \<longrightarrow> mut ch = 0)}, Relation.Id, {(x,y). True}, Inv_QueCom_mut B adds rems, \<lbrace> True \<rbrace>]" 
using ref1 validityI unfolding par_com_cvalidity_def by auto
  
  
    
    
end
  

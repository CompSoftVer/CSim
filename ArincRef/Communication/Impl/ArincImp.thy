(*
    Author:      David Sanan
    Maintainer:  David Sanan, sanan at ntu edu sg
    License:     LGPL
*)

(*  Title:      ArincMultiCoreServices.thy
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
theory ArincImp
imports "../../ArincMultiCoreState" 
begin 

definition "Guarantee_mod_chan"
where
"Guarantee_mod_chan x y j \<equiv>    
  let ch = (port_channel conf  (communication_' x) (pt (locals_' x !j))) in
  (channel_get_messages (the (chans (communication_' x) ch)) \<noteq>
    channel_get_messages (the (chans (communication_' y) ch)) \<and>    
    p_queuing conf (communication_' x) (pt (locals_' x !j))  \<longrightarrow>
       port_open (communication_' x) (pt (locals_' x !j)) \<and>             
        (evnt (locals_' x !j) = Receive_Message_Q \<longrightarrow>
           (\<exists>m. m\<subseteq># channel_get_messages (the (chans (communication_' x) ch)) \<and>
                channel_get_messages (the (chans (communication_' y) ch)) = 
                   channel_get_messages (the (chans (communication_' x) ch)) - m)) \<and>
        (evnt (locals_' x !j) = Send_Message_Q \<longrightarrow>
           channel_get_messages (the (chans (communication_' y) ch)) = 
              channel_get_messages (the (chans (communication_' x) ch)) + {#msg (locals_' x !j)#}) \<and>
        (evnt (locals_' x !j) = Clear_Message_Q \<longrightarrow>
           channel_get_messages (the (chans (communication_' y) ch)) = {#}))
"   
lemma "(\<forall>ch_id. ch_id\<noteq>(port_channel conf (communication_' x) (pt (locals_' x !i))) \<longrightarrow>
            chans (communication_' x) ch_id = chans (communication_' y) ch_id) \<Longrightarrow>
       (\<forall>ch_id. chans (communication_' x) ch_id \<noteq> chans (communication_' y) ch_id) \<longrightarrow>
                   ch_id=(port_channel conf (communication_' x) (pt (locals_' x !i)))"  
  by auto
    
lemma "(\<forall>ch_id. 
      (\<nexists>j. j<length (locals_' x1) \<and> ch_id = port_channel conf (communication_' x1) (pt (locals_' x1 !j))) \<longrightarrow> 
      chans (communication_' x1) ch_id = chans (communication_' y1) ch_id)  \<Longrightarrow> 
     (\<forall>ch_id. 
      chans (communication_' x1) ch_id \<noteq> chans (communication_' y1) ch_id \<longrightarrow>
      (\<exists>j. j<length (locals_' x1) \<and> ch_id = port_channel conf (communication_' x1) (pt (locals_' x1 !j))) 
      )" by auto

lemma "({ch. chans (communication_' x) ch = None} = {ch. chans (communication_' y) ch = None}) \<Longrightarrow>
    ({ch. \<exists>ch1. chans (communication_' x) ch = Some ch1} =
      {ch. \<exists>ch1. chans (communication_' y) ch = Some ch1})"
proof
   assume a0: "{ch. chans (communication_' x) ch = None} = {ch. chans (communication_' y) ch = None}"
    {fix ch
      assume a00:"ch \<in>{ch. \<exists>ch1. chans (communication_' x) ch = Some ch1}"
      then have " ch \<in> {ch. \<exists>ch1. chans (communication_' y) ch = Some ch1}" 
      proof-
        {assume " ch \<notin> {ch. \<exists>ch1. chans (communication_' y) ch = Some ch1}"
        then have "chans (communication_' y) ch = None" by auto
        then have "chans (communication_' x) ch = None" using a0 by auto
        then have ?thesis using a00 by auto } thus ?thesis by auto
      qed
    } then show "{ch. \<exists>ch1. chans (communication_' x) ch = Some ch1} \<subseteq> 
        {ch. \<exists>ch1. chans (communication_' y) ch = Some ch1}" by auto
  
next
   assume a0: "{ch. chans (communication_' x) ch = None} = {ch. chans (communication_' y) ch = None}"
    {fix ch
      assume a00:"ch \<in>{ch. \<exists>ch1. chans (communication_' y) ch = Some ch1}"
      have " ch \<in> {ch. \<exists>ch1. chans (communication_' x) ch = Some ch1}" 
      proof-
        {assume " ch \<notin> {ch. \<exists>ch1. chans (communication_' x) ch = Some ch1}"
        then have "chans (communication_' x) ch = None" by auto
        then have "chans (communication_' y) ch = None" using a0 by auto
        then have ?thesis using a00 by auto } thus ?thesis by auto
      qed
    } then show "{ch. \<exists>ch1. chans (communication_' y) ch = Some ch1} \<subseteq> 
        {ch. \<exists>ch1. chans (communication_' x) ch = Some ch1}" by auto       
qed

definition Guarantee_Send_Receive'
where
"Guarantee_Send_Receive' i   \<equiv> 
{(x,y). 
    let pch_id = port_channel conf (communication_' x) (pt (locals_' x !i)) in
    ports (communication_' x) = ports (communication_' y)  \<and>
   ({ch. chans (communication_' x) ch = None} = {ch. chans (communication_' y) ch = None}) \<and>
    ({ch. \<exists>ch1. chans (communication_' x) ch = Some ch1} = 
      {ch. \<exists>ch1. chans (communication_' y) ch = Some ch1}) \<and>
   ((\<exists>ch. chans (communication_' x) pch_id =  Some ch \<and> chan_queuing ch) \<longrightarrow>
     (\<exists>ch. chans (communication_' y) pch_id =  Some ch \<and> chan_queuing ch)) \<and>  
    schedule (locals_' x !i) =  schedule (locals_' y !i) \<and>
   (\<forall>ch_id. ch_id\<noteq>pch_id \<longrightarrow>
            chans (communication_' x) ch_id = chans (communication_' y) ch_id) \<and>          
    (chans (communication_' x) pch_id\<noteq> chans (communication_' y) pch_id \<longrightarrow>
      (mut (the (chans (communication_' x) pch_id)) = i + 1 \<or> 
       mut (the (chans (communication_' y) pch_id)) = i + 1)) \<and> 
   (mut (the (chans (communication_' x) pch_id)) \<noteq> mut (the (chans (communication_' y) pch_id)) \<longrightarrow>
      (mut (the (chans (communication_' x) pch_id)) = 0 \<or> 
      mut (the (chans (communication_' y) pch_id)) = 0)) \<and>       
   Guarantee_mod_chan  x y i   
   }         
"

definition Guarantee_Send_Receive
where
"Guarantee_Send_Receive i   \<equiv> 
 {(x,y). (\<exists>x1 y1.      
    x=Normal x1 \<and> y=Normal y1 \<and> 
    length (locals_' x1) = length (locals_' y1) \<and>   
    evnt (locals_' x1 !i) = evnt (locals_' y1 !i) \<and> 
    pt (locals_' x1 !i) =  pt (locals_' y1 !i) \<and>
    (\<forall>j. (j\<noteq>i) \<longrightarrow> (locals_' x1)!j = (locals_' y1)!j) \<and>      
    state_conf x1 = state_conf y1 \<and>                                 
    (x1,y1)\<in> Guarantee_Send_Receive' i    
  ) \<or> x=y           
 }  
"


definition Rely_mod_chan
  where
"Rely_mod_chan x y i \<equiv>
let ch = (port_channel conf  (communication_' x) (pt (locals_' x !i))) in
    (channel_get_messages (the (chans (communication_' x) ch)) \<noteq>
      channel_get_messages (the (chans (communication_' y) ch))) \<and>
     p_queuing conf  (communication_' x) (pt (locals_' x !i)) \<longrightarrow>      
     (\<exists>j<procs conf. 
        port_open (communication_' x) (pt (locals_' x !j)) \<and>
       ch =  (port_channel conf (communication_' x) (pt (locals_' x !j))) \<and>                  
        (evnt (locals_' x !j) = Receive_Message_Q \<longrightarrow>
           (\<exists>m. m\<subseteq># channel_get_messages (the (chans (communication_' x) ch)) \<and>
                channel_get_messages (the (chans (communication_' y) ch)) = 
                   channel_get_messages (the (chans (communication_' x) ch)) - m)
         ) \<and>
        (evnt (locals_' x !j) = Send_Message_Q \<longrightarrow>
           channel_get_messages (the (chans (communication_' y) ch)) = 
              channel_get_messages (the (chans (communication_' x) ch)) + {#msg (locals_' x !j)#}) \<and>
        (evnt (locals_' x !j) = Clear_Message_Q \<longrightarrow>
           channel_get_messages (the (chans (communication_' y) ch)) = {#})
       )   
 "  
                 
definition Rely_Send_Receive:: "nat \<Rightarrow> ('b vars_scheme \<times> 'b vars_scheme) set"
where
"Rely_Send_Receive i   \<equiv>
 {(x,y).  
   let pch_id = port_channel conf (communication_' x) (pt (locals_' x !i)) in
   Rely_mod_chan x y i  \<and>
   ports (communication_' x) = ports (communication_' y) \<and>
   {ch. chans (communication_' x) ch = None} = 
     {ch. chans (communication_' y) ch = None} \<and>
   {ch. \<exists>ch1. chans (communication_' x) ch = Some ch1} = 
     {ch. \<exists>ch1. chans (communication_' y) ch = Some ch1} \<and>  
  (\<forall>ch_id.
    ((\<exists>ch. chans (communication_' x) ch_id =  Some ch \<and> chan_queuing ch) \<longrightarrow>
     (\<exists>ch. chans (communication_' y) ch_id =  Some ch \<and> chan_queuing ch))) \<and>            
  ((mut (the (chans (communication_' x) pch_id)) = i + 1 \<or> 
   mut (the (chans (communication_' y) pch_id)) = i + 1)  \<longrightarrow>
      chans (communication_' x) pch_id = chans (communication_' y) pch_id                         
   ) \<and>    
   (\<forall>ch_id. 
      (\<nexists>j. j<procs conf \<and> ch_id = port_channel conf (communication_' x) (pt (locals_' x !j)))\<longrightarrow> 
          chans (communication_' x) ch_id = chans (communication_' y) ch_id) \<and>       
   (mut (the (chans (communication_' x) pch_id)) \<noteq> i + 1 \<longrightarrow>
      mut (the (chans (communication_' y) pch_id)) \<noteq> i + 1)    
 }
"

definition Rely_Send_ReceiveQ :: " nat \<Rightarrow> (('c vars_scheme, 'a) xstate \<times> ('c vars_scheme, 'a) xstate) set"
where
"Rely_Send_ReceiveQ i   \<equiv>
  {(x,y). ((\<exists>x1 y1. 
           x=Normal x1 \<and> y = Normal y1 \<and>
           (locals_' x1)!i = (locals_' y1)!i \<and> 
           length (locals_' x1) = length (locals_' y1) \<and>
           (\<forall>j.  (evnt (locals_' x1 !j) = evnt (locals_' y1 !j)) \<and>
                    (pt (locals_' x1 !j) = pt (locals_' y1 !j))) \<and>   
            state_conf x1 = state_conf y1 \<and>                   
           ((x1,y1)\<in> Rely_Send_Receive i)
          ) \<or> x = y)
  }"  

section {* Event Specification *}

subsection {* send queuing message param *}

definition send_q_message_i1::"(vars,(Evnt\<times>nat),Faults,Events) com"
where
"send_q_message_i1 \<equiv>                       
                     \<acute>communication :==\<^sub>E\<^sub>V \<acute>communication;;
                     (IF True THEN 
                       \<acute>communication :==\<^sub>g\<^sub>E\<^sub>V \<acute>communication                       
                     ELSE
                      \<acute>communication :==\<^sub>g\<^sub>E\<^sub>V \<acute>communication
                     FI)
                   
 "
definition send_q_message_i::"nat \<Rightarrow> (vars,(Evnt\<times>nat),Faults,Events) com"
where
"send_q_message_i i \<equiv>
   IF (\<not> (p_queuing conf \<acute>communication (pt (\<acute>locals!i)))) \<or>  
       (\<not> (p_source conf \<acute>communication (pt (\<acute>locals!i)))) \<or>
       (\<not> port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals!i))) (pt (\<acute>locals!i))) \<or> 
       ( \<not> port_open \<acute>communication (pt (\<acute>locals!i))) \<or>
       ( \<not> (snd (msg (\<acute>locals!i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals!i))))   
    THEN
        \<acute>locals :==\<^sub>E\<^sub>V \<acute>locals[i:=((\<acute>locals!i)\<lparr>ret_n := 0\<rparr>)]
   ELSE       
     (AWAIT\<^sub>\<down>\<^sub>E\<^sub>V (port_get_mutex conf \<acute>communication (pt ((\<acute>locals)!i)) = 0)
        (\<acute>communication :==\<^sub>s (port_set_mutex conf \<acute>communication (pt ((\<acute>locals)!i)) (i+1))));;
     IF port_full conf \<acute>communication (pt ((\<acute>locals)!i))  THEN          
       (\<acute>locals :== \<acute>locals[i:=((\<acute>locals!i)\<lparr>ret_n := 1\<rparr>)];;
       \<acute>communication :==\<^sub>E\<^sub>V (port_set_mutex conf \<acute>communication (pt ((\<acute>locals)!i)) 0))
     ELSE
       \<acute>communication :== 
          port_insert_message conf \<acute>communication
            (pt (\<acute>locals!i)) (msg (\<acute>locals!i)) 0  ;;
       (\<acute>locals :== 
          \<acute>locals[i:=((\<acute>locals!i)
             \<lparr>a_que_aux := set_que_aux conf \<acute>communication  (pt ((\<acute>locals)!i)) (a_que_aux (\<acute>locals ! i)) 
                            (get_que_aux conf \<acute>communication  (pt ((\<acute>locals)!i)) (a_que_aux (\<acute>locals ! i)) + 
                              {# (msg (\<acute>locals!i)) #})
             \<rparr>)];;                  
       (\<acute>locals :== \<acute>locals[i:=((\<acute>locals!i)\<lparr>ret_n := 1\<rparr>)];;
       \<acute>communication :==\<^sub>E\<^sub>V (port_set_mutex conf \<acute>communication (pt ((\<acute>locals)!i)) 0)))
     FI
   FI                  
"

lemma guar_in_rely_i5:           
   assumes a0:"j\<noteq>i" and a0':"ch = port_channel conf (communication_' x) (pt (locals_' x !j))" and
     a1:"Guarantee_mod_chan x y j" and 
     a1':"ports (communication_' x) = ports (communication_' y)" and
    a2:"(chans (communication_' x) ch\<noteq> chans (communication_' y) ch \<longrightarrow>
          (mut (the (chans (communication_' x) ch)) = j + 1 \<or> 
           mut (the (chans (communication_' y) ch)) = j + 1))" and
    a3:"(\<forall>ch_id. ch_id\<noteq>ch \<longrightarrow>
            chans (communication_' x) ch_id = chans (communication_' y) ch_id)" and
    a5:"\<forall>k. k\<noteq>j \<longrightarrow> locals_' x!k =locals_' y!k" and
    a6:"j<procs conf" 
  shows "Rely_mod_chan x y i"     
 proof-
   let ?ch_rel = "port_channel conf (communication_' x) (pt (locals_' x !i))"
  {
    assume eq_chan:"
      channel_get_messages (the (chans (communication_' x) ?ch_rel)) \<noteq>
      channel_get_messages (the (chans (communication_' y) ?ch_rel))" and
          p_queuing:"p_queuing conf (communication_' x) (pt (locals_' x !i))"          
   then have eq_port:"?ch_rel  = 
                      port_channel conf (communication_' x) (pt (locals_' x !j))"
     using a3 a0' by auto 
   have p_q:"p_queuing conf  (communication_' x) (pt (locals_' x !j))" 
     using eq_port p_queuing p_queuing_def by auto       
   then have "
          port_open (communication_' x) (pt (locals_' x ! j)) "
     using a1 eq_port eq_chan unfolding Guarantee_mod_chan_def Let_def  
     by auto   
   note x = this[simplified a0' eq_port[THEN sym]]   
   moreover have "(evnt (locals_' x ! j) = Receive_Message_Q \<longrightarrow>
            (\<exists>m. m \<subseteq># channel_get_messages (the (chans (communication_' x) ?ch_rel)) \<and>
                 channel_get_messages (the (chans (communication_' y) ?ch_rel)) =
                 channel_get_messages (the (chans (communication_' x) ?ch_rel)) - m))"
     using a1 eq_port eq_chan p_q unfolding Guarantee_mod_chan_def Let_def
     by auto
   moreover have "(evnt (locals_' x !j) = Send_Message_Q \<longrightarrow>
           channel_get_messages (the (chans (communication_' y) ?ch_rel)) = 
              channel_get_messages (the (chans (communication_' x) ?ch_rel)) + {#msg (locals_' x !j)#})"            
     using p_q a1 eq_port eq_chan unfolding Guarantee_mod_chan_def Let_def
     by auto
   moreover have "evnt (locals_' x !j) = Clear_Message_Q \<longrightarrow>
           channel_get_messages (the (chans (communication_' y) ?ch_rel)) = {#}"
    using p_q a1 eq_port eq_chan unfolding Guarantee_mod_chan_def Let_def
    by auto
  ultimately have ?thesis using  p_q eq_chan p_queuing a5   a6 a0' eq_port 
    unfolding Rely_mod_chan_def
    by (metis (no_types))
         
  } note l1 = this             
  then show ?thesis unfolding Rely_mod_chan_def by fastforce     
qed  

lemma guar_in_rely1: "i < Sys_Config.procs conf \<Longrightarrow>       
       x < Sys_Config.procs conf \<Longrightarrow> 
       x \<noteq> i \<Longrightarrow> 
       (a, b) \<in> ArincImp.Guarantee_Send_Receive x \<Longrightarrow> a=b \<Longrightarrow>
       (a, b) \<in> ArincImp.Rely_Send_ReceiveQ i"  
  unfolding Guarantee_Send_Receive_def Rely_Send_ReceiveQ_def by auto

lemma guar_in_rely2:"i < Sys_Config.procs conf \<Longrightarrow>       
       x < Sys_Config.procs conf \<Longrightarrow> 
       x \<noteq> i \<Longrightarrow> a\<noteq>b \<Longrightarrow>
       (a, b) \<in> ArincImp.Guarantee_Send_Receive x \<Longrightarrow>
       (a, b) \<in> ArincImp.Rely_Send_ReceiveQ i"  
proof-
  assume a0:"i<Sys_Config.procs conf" and
         a1:"x<Sys_Config.procs conf" and
         a2:"x\<noteq>i" and
         a3:"(a,b) \<in> Guarantee_Send_Receive x" and a4:"a\<noteq>b"      
 then obtain x1 y1 where
a3a:"a = Normal x1" and
 a3b:"b = Normal y1" and
  a30:"length (locals_' x1) = length (locals_' y1)" and   
  a3':"evnt (locals_' x1 !x) = evnt (locals_' y1 !x) \<and> 
       pt (locals_' x1 !x) =  pt (locals_' y1 !x) \<and>
       state_conf x1 = state_conf y1" and
  a3c: "(\<forall>j. (j\<noteq>x) \<longrightarrow> (locals_' x1)!j = (locals_' y1)!j)"
   unfolding Guarantee_Send_Receive_def by fastforce     
  then have a3'':"(x1,y1)\<in> Guarantee_Send_Receive' x"
    using  a3 a4 unfolding Guarantee_Send_Receive_def by auto
  note g1 = case_prodD[OF CollectD[OF a3''[simplified Guarantee_Send_Receive'_def Let_def]]]
  then have
  g1:"\<forall>ch_id.
      ch_id \<noteq> port_channel conf (communication_' x1) (pt (locals_' x1 ! x)) \<longrightarrow>
      chans (communication_' x1) ch_id = chans (communication_' y1) ch_id" and     
  g2:" schedule (locals_' x1 !x) =  schedule (locals_' y1 !x) \<and>           
    (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 !x)))\<noteq> 
    chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 !x))) \<longrightarrow>
      (mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 !x))))) = x + 1 \<or> 
       mut (the (chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 !x))))) = x + 1)) \<and> 
   (mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 !x))))) \<noteq>
    mut (the (chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 !x))))) \<longrightarrow>
      (mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 !x))))) = 0 \<or> 
      mut (the (chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 !x))))) = 0))" and
   g3:"(\<exists>ch. chans (communication_' x1)
          (port_channel conf (communication_' x1) (pt (locals_' x1 ! x))) =
         Some ch \<and>
         chan_queuing ch) \<longrightarrow>
   (\<exists>ch. chans (communication_' y1)
          (port_channel conf (communication_' x1) (pt (locals_' x1 ! x))) =
         Some ch \<and>
         chan_queuing ch)"   
    unfolding Guarantee_Send_Receive'_def Let_def
    by auto    
   have g4:"ports (communication_' x1) = ports (communication_' y1) \<and>
   ({ch. chans (communication_' x1) ch = None} = 
      {ch. chans (communication_' y1) ch = None}) \<and>
    ({ch. \<exists>ch1. chans (communication_' x1) ch = Some ch1} = 
      {ch. \<exists>ch1. chans (communication_' y1) ch = Some ch1})"    
    using  a3'' unfolding Guarantee_Send_Receive'_def Let_def
    by clarify
   moreover have eq_port_channel:"(port_channel conf (communication_' x1) (pt (locals_' x1 !x))) =
                         (port_channel conf (communication_' y1) (pt (locals_' x1 !x)))"
   using calculation by (simp add: port_channl_eq_ports)
   moreover have 
    "(\<forall>ch_id.
      ((\<exists>ch. chans (communication_' x1) ch_id =  Some ch \<and> chan_queuing ch) \<longrightarrow>
      (\<exists>ch. chans (communication_' y1) ch_id =  Some ch \<and> chan_queuing ch)))"
    using  g1 g3
    unfolding Guarantee_Send_Receive'_def Let_def 
    by metis 
  moreover have "((mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 !i))))) = i + 1 \<or> 
   mut (the (chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 !i))))) = i + 1)  \<longrightarrow>
      chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 !i))) =
      chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 !i))))   " using g1 g2       
  proof-
    have a1:"chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))) \<noteq>
    chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))) \<longrightarrow>
    mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))))) = x + 1 \<or>
    mut (the (chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))))) =
    x + 1" using  g1 g2 by metis
    have a3:" mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))))) \<noteq>
  mut (the (chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))))) \<longrightarrow>
  mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))))) = 0 \<or>
  mut (the (chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))))) = 0"
   using g1 g2 by metis
    show ?thesis  using a1 a3 a2 by auto
  qed     
  moreover have "(\<forall>ch_id. 
      (\<nexists>j. j<procs conf \<and> ch_id = port_channel conf (communication_' x1) (pt (locals_' x1 !j))) \<longrightarrow> 
      chans (communication_' x1) ch_id = chans (communication_' y1) ch_id)"
    using a3'' a1   unfolding Guarantee_Send_Receive'_def Let_def by blast              
  moreover have "mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))))) \<noteq> i + 1 \<longrightarrow>
      mut (the (chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))))) \<noteq> i + 1"    
    using calculation(4) by fastforce         
  moreover have G:"Guarantee_mod_chan x1  y1 x" using a3'' 
    unfolding Guarantee_Send_Receive'_def Let_def
    by clarsimp
  then have "Rely_mod_chan x1 y1 i" 
    using guar_in_rely_i5[OF a2 _ G] g2
    by (simp add: g2 g4 a1 a3c g1)    
  moreover have 
    "(mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))))) \<noteq>
         i + 1 \<longrightarrow>
     mut (the (chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))))) \<noteq>
     i + 1)"
    using calculation by fastforce     
  ultimately have "(x1,y1)\<in>Rely_Send_Receive i"
    unfolding Rely_Send_Receive_def Let_def by fastforce  
  thus ?thesis using a2 a3a a3b a30 a3' a3c   unfolding Rely_Send_ReceiveQ_def
   by auto
qed
lemma guar_in_rely:"i < Sys_Config.procs conf \<Longrightarrow>       
       x < Sys_Config.procs conf \<Longrightarrow> 
       x \<noteq> i \<Longrightarrow> 
       (a, b) \<in> ArincImp.Guarantee_Send_Receive x \<Longrightarrow>
       (a, b) \<in> ArincImp.Rely_Send_ReceiveQ i"  
  using guar_in_rely1 guar_in_rely2 by blast

primrec events::"Evnt \<Rightarrow> nat \<Rightarrow> (vars,(Evnt\<times>nat),Faults,Events) com"
where 
"events Send_Message_Q m = (send_q_message_i m)"


subsection {* mapping from paraeterized event to list *}


definition execute_service :: "nat \<Rightarrow> (vars,(Evnt\<times>nat),Faults,Events) com"
where
"execute_service i \<equiv> 
  IF evnt ((\<acute>locals)!i) = Send_Message_Q  THEN    
     Call (Send_Message_Q,i)
FI
"  
   

  
definition \<Gamma> :: "(Evnt\<times>nat) \<Rightarrow> ((vars,(Evnt\<times>nat),Faults,Events) com) option"
where
"
\<Gamma> \<equiv> (\<lambda> (s,m). if (m<procs conf) then Some (events s m) else None)
"

lemma body_send:"i<procs conf \<Longrightarrow>  \<Gamma> (Send_Message_Q,i) = Some (send_q_message_i i)"
unfolding \<Gamma>_def by auto


text {*modification of non-relevant vars (communication and local\_constrains)
       preserves channel spec*}


lemma rely_eq_ports1:"(Normal x1,  y) \<in> Rely_Send_ReceiveQ i \<Longrightarrow>
       \<exists>y1. y=Normal y1 \<and> ports (communication_' x1) = ports (communication_' y1) \<and>
       pt (locals_' x1 !i) = pt (locals_' y1 !i)"   
  unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Let_def by auto

lemma sta_not_cond:"LocalRG_HoareDef.Sta 
      ( \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
         p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)
     (Rely_Send_ReceiveQ i)"
  unfolding Sta_def apply clarify
  apply (frule rely_eq_ports1)
  unfolding 
     p_queuing_def   port_exists_def
    port_channel_def port_in_channel_def port_id_name_def port_open_def
    p_source_def  port_id_in_part_def port_max_size_def port_id_in_part_def
  apply auto
  apply (metis (no_types) option.sel option.simps(3))
 unfolding   Rely_Send_ReceiveQ_def 
  by fastforce+

lemma sta_cond_imp:"LocalRG_HoareDef.Sta 
      ( \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)
     (Rely_Send_ReceiveQ i)"
  unfolding Sta_def apply clarify
  apply (frule rely_eq_ports1)
  unfolding 
     p_queuing_def   port_exists_def
    port_channel_def port_in_channel_def port_id_name_def port_open_def
    p_source_def  port_id_in_part_def port_max_size_def port_id_in_part_def
  by fastforce

lemma sta_cond:"LocalRG_HoareDef.Sta 
      ( -\<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
         p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)
     (Rely_Send_ReceiveQ i)"
  unfolding Sta_def apply clarify
  apply (frule rely_eq_ports1)
  unfolding 
     p_queuing_def   port_exists_def
    port_channel_def port_in_channel_def port_id_name_def port_open_def
    p_source_def  port_id_in_part_def port_max_size_def port_id_in_part_def
  apply auto
  apply (metis (no_types) option.sel option.simps(3))
 unfolding   Rely_Send_ReceiveQ_def 
  by fastforce+

lemma sta_mut_i:"LocalRG_HoareDef.Sta 
      \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>
     (Rely_Send_ReceiveQ i)"
 unfolding Sta_def 
  apply simp         
  unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Let_def  
      port_get_mutex_def channel_get_mutex_def port_exists_def
    port_channel_def port_in_channel_def port_id_name_def   
  by force

lemma sta_mut_i':"LocalRG_HoareDef.Sta 
      \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>
     (Rely_Send_ReceiveQ i)"
 unfolding Sta_def 
  apply simp         
  unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Let_def  
      port_get_mutex_def channel_get_mutex_def port_exists_def
    port_channel_def port_in_channel_def port_id_name_def   
  by force

lemma  Sta_chan_imp: 
   "Sta (\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter> 
         {\<sigma>. chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))) = ch})
              (ArincImp.Rely_Send_ReceiveQ i)" 
  unfolding Sta_def port_get_mutex_def Let_def channel_get_mutex_def  ArincImp.Rely_Send_ReceiveQ_def 
           ArincImp.Rely_Send_Receive_def Let_def
           port_channel_def port_in_channel_def port_id_name_def port_exists_def 
  by force

lemma  Sta_aux_imp: 
   "Sta ({\<Sigma>. a_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) = a \<and>
             r_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) = r})
              (ArincImp.Rely_Send_ReceiveQ i)" 
  unfolding Sta_def port_get_mutex_def Let_def channel_get_mutex_def  ArincImp.Rely_Send_ReceiveQ_def 
           ArincImp.Rely_Send_Receive_def Let_def
           port_channel_def port_in_channel_def port_id_name_def port_exists_def 
  by force

lemma  Sta_a_imp: 
   "Sta ({\<Sigma>. a_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) = a})
              (ArincImp.Rely_Send_ReceiveQ i)" 
  unfolding Sta_def port_get_mutex_def Let_def channel_get_mutex_def  ArincImp.Rely_Send_ReceiveQ_def 
           ArincImp.Rely_Send_Receive_def Let_def
           port_channel_def port_in_channel_def port_id_name_def port_exists_def 
  by force

lemma  Sta_r_imp: 
   "Sta ({\<Sigma>. r_que_aux ((locals_' \<Sigma>)!i) (port_channel conf (communication_' \<Sigma>) (pt (locals_' \<Sigma> ! i))) = a})
              (ArincImp.Rely_Send_ReceiveQ i)" 
  unfolding Sta_def port_get_mutex_def Let_def channel_get_mutex_def  ArincImp.Rely_Send_ReceiveQ_def 
           ArincImp.Rely_Send_Receive_def Let_def
           port_channel_def port_in_channel_def port_id_name_def port_exists_def 
  by force

lemma  Sta_chan_data_imp: 
   "Sta (\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter> 
         {\<sigma>. data( the (chans (communication_' \<sigma>) (port_channel conf (communication_' \<sigma>) (pt (locals_' \<sigma> ! i))))) = d})
              (ArincImp.Rely_Send_ReceiveQ i)" 
  unfolding Sta_def port_get_mutex_def Let_def channel_get_mutex_def  ArincImp.Rely_Send_ReceiveQ_def 
           ArincImp.Rely_Send_Receive_def Let_def
           port_channel_def port_in_channel_def port_id_name_def port_exists_def 
  by force

lemma Sta_port_full:"Sta (\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter>             
           \<lbrace>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)
       (ArincImp.Rely_Send_ReceiveQ i)"
unfolding Sta_def
     p_queuing_def   port_exists_def port_get_mutex_def
    port_channel_def port_in_channel_def port_id_name_def port_open_def
    p_source_def  port_id_in_part_def port_max_size_def port_id_in_part_def
 channel_get_messages_def port_full_def channel_full_def Let_def channel_get_mutex_def
channel_get_messages_def channel_get_bufsize_def Rely_Send_ReceiveQ_def Rely_Send_Receive_def
  by auto

lemma Sta_port_not_full:"Sta (\<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter>             
           \<lbrace>\<not>port_full conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)
       (ArincImp.Rely_Send_ReceiveQ i)"
unfolding Sta_def
     p_queuing_def   port_exists_def port_get_mutex_def
    port_channel_def port_in_channel_def port_id_name_def port_open_def
    p_source_def  port_id_in_part_def port_max_size_def port_id_in_part_def
 channel_get_messages_def port_full_def channel_full_def Let_def channel_get_mutex_def
channel_get_messages_def channel_get_bufsize_def Rely_Send_ReceiveQ_def Rely_Send_Receive_def
  by auto

lemma Sta_true:"Sta \<lbrace>True\<rbrace>
       (ArincImp.Rely_Send_ReceiveQ i)"
unfolding Sta_def Rely_Send_ReceiveQ_def by auto

lemma Sta_imp_ret_n: "Sta \<lbrace>ret_n (\<acute>locals ! i) = Suc 0\<rbrace> (ArincImp.Rely_Send_ReceiveQ i)"
unfolding Sta_def Rely_Send_ReceiveQ_def by auto

lemma imp_port_set_mutex_guarantee:"port_get_mutex conf c (pt (l ! i)) = 0 \<Longrightarrow>      
       state_conf \<lparr>communication_' = c, locals_' = l, timer_' = t\<rparr> \<Longrightarrow>       
       p_queuing conf c (pt (l ! i)) \<Longrightarrow>       
       (Normal \<lparr>communication_' = c, locals_' = l, timer_' = t\<rparr>,
        Normal
         \<lparr>communication_' = port_set_mutex conf c (pt (l ! i)) (Suc i), locals_' = l,
            timer_' = t\<rparr>)
       \<in> ArincImp.Guarantee_Send_Receive i"
  unfolding state_conf_def  Guarantee_Send_Receive'_def Guarantee_Send_Receive_def  port_set_mutex_def 
                port_get_mutex_def channel_get_mutex_def chan_queuing_def channel_get_messages_def
              channel_set_mutex_def ch_id_queuing_def Let_def p_queuing_def chan_sampling_def
            Guarantee_mod_chan_def  Let_def port_exists_def    
  by auto

lemma imp_guarante_ref:"( s,  s) \<in> ArincImp.Guarantee_Send_Receive i" 
  unfolding Guarantee_Send_Receive_def 
  by auto



lemma imp_rely_ref:"( s,  s) \<in> Rely_Send_ReceiveQ i" 
  unfolding Rely_Send_ReceiveQ_def 
  by auto

(*
lemma Send_Receive_Correct:
 "\<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> 
    (COBEGIN SCHEME [0 \<le> i < procs conf]
      (execute_service i, pre_i B i,
      Rely B i, Guarantee B i,
      Post_Arinc B, \<lbrace> True \<rbrace>)
     COEND)
  SAT [Pre_Arinc B, Id,
   {(x,y). \<exists>nx ny. x=Normal nx \<and> y=Normal ny}, Post_Arinc B, \<lbrace> True \<rbrace>]"
apply (subgoal_tac "procs conf>0")
 apply (rule Parallel)              
      apply (auto simp add:  LocalRG_HoareDef.Pre_def LocalRG_HoareDef.Rely_def Com_def Guar_def  Post_def Abr_def,
            (auto simp add: Rely_System_def Rely_def Rely_Send_Receive_def state_conf_def)[1])
       apply (auto simp add: Guar_in_Rely_i Pre_Arinc_def pre_i_def execute)     
by (auto simp add:  n_n Guarantee_def) *)
    
end
  
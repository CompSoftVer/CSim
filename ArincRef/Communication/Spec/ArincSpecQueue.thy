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
theory ArincSpecQueue
imports ArincSpec_com_queue_insert "HOL-Library.Countable"
begin 
  
section {* tests *}
 
primrec events::"Evnt \<Rightarrow> nat \<Rightarrow> (vars,(Evnt\<times>nat),Faults,Events) com"
where 
"events Send_Message_Q m = (send_q_message_i m)"


subsection {* mapping from parameterized event to list *}


definition execute_service :: "nat \<Rightarrow> (vars,(Evnt\<times>nat),Faults,Events) com"
where
"execute_service i \<equiv> 
  IF evnt ((\<acute>locals)!i) = Send_Message_Q  THEN    
     Call (Send_Message_Q,i)  
  FI
"  
  
definition \<Gamma> :: " (Evnt\<times>nat) \<Rightarrow> ((vars,(Evnt\<times>nat),Faults,Events) com) option"
where
"
\<Gamma> \<equiv> (\<lambda> (s,m). if (m<procs conf) then Some (events s m) else None)
"

lemma body_send:"i < procs conf \<Longrightarrow>  \<Gamma> (Send_Message_Q,i) = Some (send_q_message_i i)"
  unfolding \<Gamma>_def by auto

subsection {* correctness on the call for each event based on the correctness of the body 
             of the functions*}
lemma call_send_correct:
  "i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> LanguageCon.com.Call
      (Send_Message_Q,i) sat [Invariant B adds rems i  \<inter>
                          \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace>, Rely_Send_ReceiveQ i, 
                          Guarantee_Send_Receive  i, Post_Arinc_i B adds rems i,UNIV]"      
apply (rule CallRec,(auto simp add: body_send reflexive_Guarantee_Send                                   
                                 ))
    apply (simp_all add: sta_event_inv)  
  using send_correct by (rule conseqPrePost, auto) 

     
 lemma call_send_correct':
  " i < Sys_Config.procs conf \<Longrightarrow>
    \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> LanguageCon.com.Call
                  (Send_Message_Q, i) sat [Pre_QueCom_ch B adds rems ch_id \<inter>
                           \<lbrace>evnt (\<acute>locals ! i) =
                            Send_Message_Q\<rbrace>, Rely_Send_ReceiveQ
                                              i, Guarantee_Send_Receive i, Pre_QueCom_ch B adds rems ch_id,UNIV]"
apply (rule CallRec,(auto simp add: body_send reflexive_Guarantee_Send))  
   apply (simp_all add:sta_event_inv_PreQue) 
  using send_correct'  by (rule conseqPrePost, auto) 
     
lemma execute'':
   "i < procs conf \<Longrightarrow>
    \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> execute_service i sat [Invariant B adds rems i, 
                                       Rely_Send_ReceiveQ i, 
                                       Guarantee_Send_Receive i, Post_Arinc_i B adds rems i,UNIV]"   
unfolding execute_service_def  
  apply (rule If, auto simp add:  reflexive_Guarantee_Send sta_invariant_rely_send,
         auto dest: call_send_correct )         
  apply (auto simp add: Sta_intro sta_not_event sta_not_event_inv Post_Arinc_i_def) 
  apply (rule conseqPre, auto)             
  by  (rule Skip, auto simp add: sta_invariant_rely_send reflexive_Guarantee_Send)
  

               
lemma execute''':
   "i < procs conf \<Longrightarrow>
    \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> execute_service i sat [Pre_QueCom_ch B adds rems ch_id, 
                                       Rely_Send_ReceiveQ i, 
                                       Guarantee_Send_Receive i, Pre_QueCom_ch B adds rems ch_id,UNIV]"   
  unfolding execute_service_def  
     apply (rule If, auto simp add:  reflexive_Guarantee_Send sta_no_channel_rely_send,         
         auto dest: call_send_correct' intro:conseqPre)    
 apply (rule conseqPre, auto)             
  by  (rule Skip, auto simp add: sta_no_channel_rely_send reflexive_Guarantee_Send)


lemma execute':
   "i < procs conf \<Longrightarrow>
    \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> execute_service i sat [{s. \<forall>ch_id.  s\<in>Pre_QueCom_ch B adds rems ch_id}, 
                                       Rely_Send_ReceiveQ i, 
                                       Guarantee_Send_Receive i,{s. \<forall>ch_id. s\<in>Pre_QueCom_ch B adds rems ch_id},UNIV]"       
  using execute''' Pre_Post_all by blast

          
 lemma execute:
   "i < procs conf \<Longrightarrow>
    \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> execute_service i sat [{s. \<forall>ch_id. s\<in>Pre_QueCom_ch B adds rems ch_id} \<inter> 
                                           Invariant B adds rems i, 
                                       Rely_Send_ReceiveQ i, 
                                       Guarantee_Send_Receive i, 
                                       {s. \<forall>ch_id. s\<in>Pre_QueCom_ch B adds rems ch_id} \<inter> 
                                          Post_Arinc_i B adds rems i, UNIV]"   
  apply (rule Conj_post[of _ _ _ _ _ _ _ _ UNIV _ UNIV, simplified])      
   apply (frule execute',rule conseqPrePost,auto)    
   by (frule execute'',rule conseqPrePost,auto) 


      
lemma Send_Receive_Correct:
 "\<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> 
    (COBEGIN SCHEME [0 \<le> i < procs conf]
      (execute_service i, {s. \<forall>ch_id. s\<in>Pre_QueCom_ch B adds rems ch_id} \<inter> Invariant B adds rems i,
      Rely_Send_ReceiveQ i, Guarantee_Send_Receive i,
     {s. \<forall>ch_id. s\<in>Pre_QueCom_ch B adds rems ch_id} \<inter> Post_Arinc_i B adds rems i, \<lbrace> True \<rbrace>)
     COEND)
  SAT [Inv_QueCom  B adds rems, Id,
  {(x,y). True}, Inv_QueCom  B adds rems, \<lbrace> True \<rbrace>]"
apply (subgoal_tac "procs conf>0")                  
   apply (rule Parallel)              
        apply (auto simp add:   LocalRG_HoareDef.Pre_def LocalRG_HoareDef.Rely_def 
                                Com_def Guar_def Post_def Abr_def execute,
            (auto simp add: Id_def Rely_Send_ReceiveQ_def Rely_Send_Receive_def state_conf_def )[1])
        apply (simp add: Guar_Rely_Send_ReceiveQ)         
        apply (auto simp add: Guarantee_Send_Receive_def  intro: n_n)
    apply (auto simp add:Inv_QueCom_def Pre_QueCom_ch_def Inv_QueCom_ch_def  Invariant_def)[2]    
  unfolding Pre_QueCom_ch_def Inv_QueCom_ch_def Inv_QueCom_def Post_Arinc_i_def Invariant_def
  by force


 lemma execute_mut:
   "i < procs conf \<Longrightarrow>
    \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> execute_service i sat [{s. \<forall>ch_id. s\<in>Pre_QueCom_ch_mut B adds rems ch_id} \<inter> 
                                           Invariant_mut B adds rems i \<inter>
                                        {s. \<forall>ch_id. \<forall>ch. (chans (communication_' s) ch_id = Some ch \<longrightarrow> mut ch = 0)}, 
                                       Rely_Send_ReceiveQ i, 
                                       Guarantee_Send_Receive i, 
                                       {s. \<forall>ch_id. s\<in>Pre_QueCom_ch_mut B adds rems ch_id} \<inter> 
                                          Post_Arinc_i_mut B adds rems i, UNIV]"
   apply (frule execute)
   apply (rule conseqPrePost,auto)       
   by (auto simp add: Pre_QueCom_ch_mut_def Invariant_mut_def Pre_QueCom_ch_def Invariant_def Inv_QueCom_ch_mut_def
   Inv_QueCom_ch_def channel_spec_mut_def channel_spec_def Post_Arinc_i_mut_def Post_Arinc_i_def )

lemma Send_Receive_Correct_mut:
 "\<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> 
    (COBEGIN SCHEME [0 \<le> i < procs conf]
      (execute_service i, {s. \<forall>ch_id. s\<in>Pre_QueCom_ch_mut B adds rems ch_id} \<inter> 
                          Invariant_mut B adds rems i \<inter>
                          {s. \<forall>ch_id. \<forall>ch. (chans (communication_' s) ch_id = Some ch \<longrightarrow> mut ch = 0)},
      Rely_Send_ReceiveQ i, Guarantee_Send_Receive i,
     {s. \<forall>ch_id. s\<in>Pre_QueCom_ch_mut B adds rems ch_id} \<inter> 
       Post_Arinc_i_mut B adds rems i, \<lbrace> True \<rbrace>)
     COEND)  
  SAT [Inv_QueCom_mut  B adds rems \<inter>  
            {s. \<forall>ch_id. \<forall>ch. (chans (communication_' s) ch_id = Some ch \<longrightarrow> mut ch = 0)}, Id,
  {(x,y). True}, Inv_QueCom_mut  B adds rems, \<lbrace> True \<rbrace>]"
apply (subgoal_tac "procs conf>0")                  
   apply (rule Parallel)              
        apply (auto simp add:   LocalRG_HoareDef.Pre_def LocalRG_HoareDef.Rely_def 
                                Com_def Guar_def Post_def Abr_def execute_mut,
            (auto simp add: Id_def Rely_Send_ReceiveQ_def Rely_Send_Receive_def state_conf_def )[1])
        apply (simp add: Guar_Rely_Send_ReceiveQ)         
        apply (auto simp add: Guarantee_Send_Receive_def  intro: n_n)
    apply (auto simp add:Inv_QueCom_mut_def Pre_QueCom_ch_mut_def Inv_QueCom_ch_mut_def  Invariant_mut_def)[2]    
  unfolding Pre_QueCom_ch_mut_def Inv_QueCom_ch_mut_def Inv_QueCom_mut_def Post_Arinc_i_mut_def Invariant_mut_def
  by force

end      
  
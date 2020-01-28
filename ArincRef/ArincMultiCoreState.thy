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
theory ArincMultiCoreState
 
imports "EmbSimpl.HeapList" "CSimpl.XVcgCon" "EmbSimpl.VcgSeq" 
        "HOL-Library.Multiset" "HOL-Eisbach.Eisbach" 
begin
section {* Definitions *}

subsection {* Data type, basic components *}
datatype Events = EV ("E\<^sub>V")
type_synonym  partition_id =  nat
type_synonym channel_id = nat
type_synonym port_id = nat
type_synonym domain_id = nat
type_synonym port_name = "string"
type_synonym partition_name = "string"
type_synonym max_buffer_size = nat
type_synonym msg_size = nat
type_synonym buffer_size = nat
datatype port_direction = SOURCE | DESTINATION
typedecl msg
type_synonym Message = "msg\<times>nat"
type_synonym timer = nat

datatype Port = Port_Que  port_name port_direction
              | Port_Samp port_name port_direction

datatype Channel = Channel_Sampling channel_id port_name "port_name set" msg_size timer
                 | Channel_Queuing channel_id max_buffer_size port_name port_name msg_size 

subsection {* System Configuration *}

subsubsection {* Communication Configuration *}

record Communication_Config = 
          ports_conf :: "Port set"
          channels_conf :: "Channel set"

subsubsection {* Partition Configuration *}


datatype partition_type = USER_PARTITION | SYSTEM_PARTITION
datatype partition_mode_type =  IDLE | WARM_START | COLD_START | NORMAL
datatype Partition_Conf = PartConf partition_id partition_name partition_type "port_name set"


subsubsection {* System Configuration *}
record Sys_Config = partconf :: "Partition_Conf set"
                    commconf :: Communication_Config   
                    procs::nat
                    

subsection {* System State *}

subsubsection {* Partition State *}
record Partition = 
    part_mode :: partition_mode_type

type_synonym Partitions = "partition_id \<rightharpoonup> Partition"

subsubsection {* Communication Definition *}

text {* Port record: *}

text {* Mutex to control access to queue *}

type_synonym mutex = nat

text {* Channel record: *}
 

(* text {* Channel data: the data a channel contains can be 
Sampling, which contains the message if any, and the time the message was inserted;
Queuing, which contains a multiset with the messages in the queue.
 Additinally queuing contains two additional multiset representing the set of messages being
added or removed in the queue. These variables are auxiliary variables keeping the log. we 
use them to check that inserted/remove elements is consistent with the queue. That is the queue
preserves the equation q = a - r /\ $r\<subseteq>a$*} *)

  
datatype Channel_data =
  Samp  "Message option" timer
  | Queue "Message multiset"
    
record Port_data =
  portid:: "port_id option"
  timer::timer
 
  

record channel =
  mut :: mutex
  data :: Channel_data

text {* Communication record: structure *}

record communication = 
  chans::"channel_id \<rightharpoonup> channel"
  ports::"port_name \<rightharpoonup> Port_data"
  ports_mut::mutex
 
subsubsection {* Scheduler Definition *}

text {* very abstract specification of the scheduler *}
type_synonym scheduler = partition_id


subsubsection {* Global state *}
(* record globals_d =   
  partitions_' :: "partition_id \<rightharpoonup> partition"
  communication_' :: "communication"
  scheduler_' :: scheduler *)

subsubsection {* Events *}
datatype Evnt = Write_Message_S | Read_Message_S | Send_Message_Q | 
                Receive_Message_Q | Clear_Message_Q | Create_Port

subsubsection {* local state *}
record locals = 
  evnt::Evnt 
  pt::port_id
  msg::Message
  msg_t::timer
  ret_n::nat
  ret_msg::"Message option"    
  a_que_aux:: "channel_id \<Rightarrow> Message multiset"
  r_que_aux:: "channel_id \<Rightarrow> Message multiset"
  schedule :: scheduler    
  port_name_' :: port_name

subsubsection {* state *}

record vars =               
  communication_' :: "communication"  
  locals_' ::"locals list"
  timer_'::timer

    

datatype Faults = No_F

section {* Utility Functions used for Event Specification *}

subsection {* Partition Functions *}

primrec part_id
where
"part_id (PartConf p_id _ _ _) = p_id" 

primrec part_name
where
"part_name (PartConf _ p_name _ _) = p_name" 

primrec part_type
where
"part_type (PartConf _ _ p_type _) = p_type"

primrec part_ports
where
"part_ports (PartConf _ _ _ p_set) = p_set"

subsection {* Communication  Functions *}
  
primrec channel_id 
where
"channel_id (Channel_Sampling ch_id _ _ _ _)  = ch_id"
|"channel_id (Channel_Queuing ch_id _ _ _ _)  = ch_id"

primrec channel_source 
where
"channel_source (Channel_Sampling _ p_s _ _ _)  = p_s"
|"channel_source (Channel_Queuing _ _ p_s _ _)  = p_s"

primrec channel_destination
where
"channel_destination (Channel_Sampling _ _ p_d _ _)  = p_d"
|"channel_destination (Channel_Queuing _ _ _ p_d _)  = {p_d}"

primrec channel_ports
where
"channel_ports (Channel_Sampling _ p_s p_d _ _)  = {p_s} \<union> p_d"
|"channel_ports (Channel_Queuing _ _ p_s p_d _)  = {p_s} \<union> {p_d}"

primrec channel_size
where
"channel_size (Channel_Queuing _ c_s _ _ _) = c_s"
|"channel_size (Channel_Sampling _ _ _ _ _) = 1"
  
primrec channel_msg_size
where
"channel_msg_size (Channel_Queuing _ _ _ _ c_m_s) = c_m_s"
|"channel_msg_size (Channel_Sampling _ _ _ c_m_s _) = c_m_s"
  
primrec channel_msg_time
  where
 "channel_msg_time (Channel_Queuing _ _ _ _ _) = 0"
|"channel_msg_time (Channel_Sampling _ _ _ _ t) = t"

primrec channel_queuing
where
"channel_queuing (Channel_Sampling _ _ _ _ _) = False"
|"channel_queuing (Channel_Queuing _ _ _ _ _) = True"

primrec channel_sampling
where
"channel_sampling (Channel_Sampling _ _ _ _ _) = True"
|"channel_sampling (Channel_Queuing _ _ _ _ _) = False"

primrec port_name
where
"port_name (Port_Que p_n _) = p_n"
|"port_name (Port_Samp p_n _) = p_n"

primrec port_dir
where
"port_dir (Port_Que _ p_d) = p_d"
|"port_dir (Port_Samp _ p_d) = p_d"

primrec port_queuing
where
"port_queuing (Port_Samp _ _) = False"
|"port_queuing (Port_Que _ _) = True"

primrec port_sampling
where
"port_sampling (Port_Samp _ _) = True"
|"port_sampling (Port_Que _ _) = False"

primrec port_dest 
where
"port_dest (Port_Que _ d) = (d=DESTINATION)"
|"port_dest (Port_Samp _  d) =(d=DESTINATION)"

primrec port_sour
where
"port_sour (Port_Que _ d) = (d=SOURCE)"
|"port_sour  (Port_Samp _  d) =(d=SOURCE)"


lemma no_p_sampling_queuing:"port_sampling p \<and> port_queuing p \<Longrightarrow> False" 
unfolding port_sampling_def port_queuing_def
apply (cases p)
by auto

lemma no_c_sampling_queuing:"channel_sampling c \<and> channel_queuing c \<Longrightarrow> False" 
unfolding channel_sampling_def channel_queuing_def
apply (cases c)
by auto

primrec channel_valid_ports :: "Channel \<Rightarrow> bool"
where
"channel_valid_ports (Channel_Sampling _ ps pds _ _)  = (ps \<notin> pds)"
|"channel_valid_ports (Channel_Queuing _ _ ps pd _)  = (ps\<noteq>pd)"

text {* This definitions requires that ch\_id of each channel in system\_conf are different,
        similarly for port\_id *}

definition get_channel::"Sys_Config \<Rightarrow> channel_id \<Rightarrow> Channel"
where                                                                       
"get_channel cnf ch_id \<equiv> THE ch. (ch\<in> (channels_conf (commconf cnf))) \<and> channel_id ch = ch_id
"

definition get_port::"Sys_Config \<Rightarrow> port_name \<Rightarrow> Port"
where
"get_port cnf p_n \<equiv> THE p. (p\<in> (ports_conf (commconf cnf))) \<and> port_name p = p_n
"

definition ch_id_queuing :: "Sys_Config \<Rightarrow> channel_id \<Rightarrow> bool"
where                             
"ch_id_queuing cnf ch_id \<equiv> \<exists>ch.(ch\<in> (channels_conf (commconf cnf))) \<and> channel_id ch = ch_id \<and>  
                               channel_queuing ch
"

definition ch_id_sampling :: "Sys_Config \<Rightarrow> channel_id \<Rightarrow> bool"
where
"ch_id_sampling cnf ch_id \<equiv> \<exists>ch.  (ch\<in> (channels_conf (commconf cnf))) \<and> channel_id ch = ch_id \<and>  channel_sampling ch
"


definition port_name_in_channel :: "Sys_Config \<Rightarrow> port_name  \<Rightarrow> channel_id \<Rightarrow>bool"
where                           
"port_name_in_channel cnf p_n ch_id \<equiv> \<exists>ch.  (ch\<in> (channels_conf (commconf cnf))) \<and> 
                                         channel_id ch = ch_id \<and> p_n\<in> channel_ports ch 
"     

definition port_exists::"communication \<Rightarrow> port_name \<Rightarrow> bool"
where
"port_exists c p_n \<equiv> \<exists>p. (ports c) p_n = Some p"

definition port_open :: "communication \<Rightarrow> port_id \<Rightarrow> bool"
where
"port_open c p_id \<equiv> \<exists>p_n. port_exists c p_n \<and> portid (the ((ports c) p_n)) = Some p_id" 

definition port_id_name :: "communication \<Rightarrow> port_id \<Rightarrow> port_name"
where    
"port_id_name c p_id \<equiv> (THE p_n. port_exists c p_n \<and> portid (the ((ports c) p_n)) = (Some p_id))"  

definition port_id_in_part:: "Sys_Config \<Rightarrow> communication \<Rightarrow> partition_id \<Rightarrow> port_id \<Rightarrow> bool"
where
"port_id_in_part cfg c pa_id p_id \<equiv> 
  \<exists>p\<in>partconf cfg. pa_id = part_id p \<and> (port_id_name c p_id)\<in>(part_ports p)
"   
definition port_in_channel:: "Sys_Config \<Rightarrow> communication \<Rightarrow> port_id  \<Rightarrow> channel_id \<Rightarrow>bool"
  where
"port_in_channel cnf c p_id ch_id \<equiv> port_name_in_channel cnf (port_id_name c p_id) ch_id"

definition channel_id_get_source :: "Sys_Config \<Rightarrow> channel_id \<Rightarrow> port_name"
where
"channel_id_get_source cnf ch_id \<equiv> 
  THE p_n. port_name_in_channel cnf p_n ch_id \<and>
            (\<exists>p. (p\<in> (ports_conf (commconf cnf))) \<and> port_name p = p_n \<and> port_sour p)
"

definition channel_id_get_destinations :: "Sys_Config \<Rightarrow> channel_id \<Rightarrow> port_name set"
where
"channel_id_get_destinations cnf ch_id \<equiv> 
   {p_n. port_name_in_channel cnf p_n ch_id \<and>
          (\<exists>p. (p\<in> (ports_conf (commconf cnf))) \<and> port_name p = p_n \<and> port_dest p)}
"                                                      

definition conf_ex_port_id::"Sys_Config \<Rightarrow> port_name \<Rightarrow> bool"
where
"conf_ex_port_id cnf p_n \<equiv> \<exists>p. p \<in> ports_conf (commconf cnf) \<and> port_name p = p_n
"

definition port_channel :: "Sys_Config \<Rightarrow> communication \<Rightarrow> port_id \<Rightarrow> channel_id"
where                                        
"port_channel cnf c  p_n \<equiv> THE ch. port_in_channel cnf c p_n ch"
                                          

definition p_queuing :: "Sys_Config \<Rightarrow> communication \<Rightarrow> port_id \<Rightarrow> bool"
where                                             
"p_queuing cnf c p_id \<equiv> ch_id_queuing cnf (port_channel cnf c p_id)
"

definition p_sampling :: "Sys_Config \<Rightarrow> communication \<Rightarrow> port_id \<Rightarrow> bool"
where
"p_sampling cnf c p_id \<equiv>  ch_id_sampling cnf (port_channel cnf c p_id)
"

definition p_source ::"Sys_Config \<Rightarrow> communication \<Rightarrow> port_id \<Rightarrow> bool"
where                                  
"p_source cnf c p_id \<equiv>  
  (port_id_name c p_id) = channel_id_get_source cnf (port_channel cnf c p_id)"

definition p_destination ::"Sys_Config \<Rightarrow> communication \<Rightarrow> port_id \<Rightarrow> bool"
where
"p_destination cnf c p_id \<equiv>
   (port_id_name c p_id) \<in> channel_id_get_destinations cnf (port_channel cnf c p_id)"

subsection {* Partition Access *}

definition part_id_in_parts::"(partition_id \<rightharpoonup> Partition_Conf) \<Rightarrow> partition_id  \<Rightarrow> bool"
where
"part_id_in_parts f p_id \<equiv> \<exists>x. f p_id = Some x
"


definition port_in_part:: "Sys_Config \<Rightarrow> partition_id \<Rightarrow> port_name \<Rightarrow> bool"
where
"port_in_part cfg pa_id p_n \<equiv> 
  \<exists>p\<in>partconf cfg. pa_id = part_id p \<and> p_n\<in>(part_ports p)
" 

   
subsection {* Channel  Functions *}
 
definition channel_get_messages :: "channel \<Rightarrow> Message multiset"
where
"channel_get_messages ch \<equiv>
  case (data ch) of 
     (Queue q ) \<Rightarrow> q
    |(Samp s t) \<Rightarrow>(case s of Some m \<Rightarrow> {#m#}
                 |_ \<Rightarrow> {#})"
  
definition chan_msg_get_time :: "channel \<Rightarrow> timer"
where
"chan_msg_get_time ch \<equiv>
  case (data ch) of 
     (Queue q ) \<Rightarrow> 0
    |(Samp s t) \<Rightarrow>t"

definition channel_set_messages :: "channel \<Rightarrow> Message multiset \<Rightarrow> timer \<Rightarrow> channel"
where
"channel_set_messages ch msgs t \<equiv>
  case (data ch) of 
    Queue q \<Rightarrow> ch\<lparr>data:= Queue msgs\<rparr>
   |Samp m ts \<Rightarrow> 
     (case size msgs of 
       0 \<Rightarrow> ch\<lparr>data:=Samp None t\<rparr>
      |_ \<Rightarrow> ch\<lparr>data:=Samp (Some (SOME m. m\<in># msgs)) t\<rparr>)
"
  
definition channel_insert_message :: "channel \<Rightarrow> Message \<Rightarrow> timer \<Rightarrow> channel"
where
"channel_insert_message ch m t \<equiv>
  case (data ch) of 
    Queue _  \<Rightarrow> channel_set_messages ch ((channel_get_messages ch) +{#m#}) t
   |Samp _ _ \<Rightarrow> channel_set_messages ch {# m #} t"


definition channel_remove_message :: "channel \<Rightarrow> Message \<Rightarrow> channel"
where
"channel_remove_message ch m \<equiv>
  case (data ch) of Queue q  \<Rightarrow>
    channel_set_messages ch ((channel_get_messages ch) -{#m#}) 0
  |(Samp s ts) \<Rightarrow>
    (case s of Some m' \<Rightarrow>
      if m'=m then ch\<lparr>data:= Samp None ts\<rparr>
      else ch
    | _ \<Rightarrow> ch \<lparr>data := Samp None ts\<rparr>)
"

definition channel_clear_messages :: "channel \<Rightarrow> channel"
where
"channel_clear_messages ch  \<equiv>
   case (data ch) of 
     Queue q \<Rightarrow> ch\<lparr>data:= Queue {#} \<rparr>
   | Samp _ ts \<Rightarrow> ch\<lparr>data:= Samp None ts\<rparr>
"

definition channel_get_mutex :: "channel \<Rightarrow> mutex"
where
"channel_get_mutex ch \<equiv> mut ch"

definition channel_set_mutex :: "channel \<Rightarrow> mutex \<Rightarrow> channel"
where
"channel_set_mutex ch m = ch\<lparr>mut:=m\<rparr>"


definition channel_get_bufsize :: "channel \<Rightarrow>  buffer_size"
where   
"channel_get_bufsize ch = size (channel_get_messages ch)"

       
definition channel_full :: "Sys_Config \<Rightarrow> communication \<Rightarrow> channel_id  \<Rightarrow> bool"
where
"channel_full cnf com ch_id \<equiv> 
   \<exists>ch. (ch\<in> (channels_conf (commconf cnf))) \<and> channel_id ch = ch_id \<and>
        channel_size ch \<le> channel_get_bufsize (the  (chans com ch_id))
"
    
definition channel_empty :: "communication \<Rightarrow> channel_id  \<Rightarrow> bool"
where
"channel_empty com ch_id \<equiv>   
   channel_get_bufsize (the (chans com ch_id)) = 0  
"

definition chan_sampling
where
"chan_sampling ch \<equiv>
  case (data ch) of Samp _ _ \<Rightarrow> True
 | _ \<Rightarrow> False"

definition chan_queuing
where
"chan_queuing ch \<equiv>
  \<not> (chan_sampling ch)"


subsection {* Communication Functions *}



definition port_get_mutex :: "Sys_Config \<Rightarrow> communication  \<Rightarrow> port_id \<Rightarrow> mutex"
where
"port_get_mutex cnf c p_id  \<equiv> 
   let ch_id = port_channel cnf c p_id in
       channel_get_mutex (the (chans c ch_id))
"     
 
definition port_set_mutex :: "Sys_Config \<Rightarrow> communication  \<Rightarrow> port_id \<Rightarrow> mutex \<Rightarrow> communication "
where                                           
"port_set_mutex cnf c p_id m  \<equiv> 
    let ch_id = port_channel cnf  c p_id;
        ch = the ((chans c) ch_id) in            
        c\<lparr> chans := (chans c) (ch_id:= Some (channel_set_mutex ch m)) \<rparr>
"                      

definition port_insert_message :: "Sys_Config \<Rightarrow> communication  \<Rightarrow> port_id \<Rightarrow> Message \<Rightarrow> timer \<Rightarrow> communication "
where
"port_insert_message cnf c p_id m t \<equiv> 
   let ch_id = port_channel cnf  c p_id;
        ch = (the ((chans c) ch_id)) in             
        c\<lparr> chans:= (chans c) (ch_id:= Some (channel_insert_message ch m t)) \<rparr>
"    

definition port_get_message :: "Sys_Config \<Rightarrow> communication  \<Rightarrow> port_id \<Rightarrow> Message option"
where
"port_get_message cnf c p_id \<equiv> 
     let ch_id = port_channel cnf  c p_id;
         ch = the ((chans c) ch_id) in             
        if channel_get_messages ch = {#} then 
          None
        else Some (SOME m. m\<in>#  channel_get_messages ch)
"

definition port_get_set_message :: "Sys_Config \<Rightarrow> communication  \<Rightarrow> port_id \<Rightarrow> Message multiset"
where
"port_get_set_message cnf c p_id \<equiv> 
     let ch_id = port_channel cnf c p_id;
         ch = the ((chans c) ch_id) in             
        if channel_get_messages ch = {#} then {#}
        else {# (SOME m. m\<in>#  channel_get_messages ch) #}
"

definition port_remove_message :: "Sys_Config \<Rightarrow> communication  \<Rightarrow> port_id \<Rightarrow> Message \<Rightarrow> communication"
where
"port_remove_message cnf c p_id m \<equiv> 
    let ch_id = port_channel cnf c p_id;
        ch = the ((chans c) ch_id) in                 
        c\<lparr> chans:= (chans c) (ch_id:= Some (channel_remove_message ch m)) \<rparr>         
       
"

definition port_clear_messages :: "Sys_Config \<Rightarrow> communication  \<Rightarrow> port_id \<Rightarrow>  communication"
where
"port_clear_messages cnf c p_id  \<equiv> 
    let ch_id = port_channel cnf c p_id;
        ch = the ((chans c) ch_id) in                 
        c\<lparr> chans:= (chans c) (ch_id:= Some (channel_clear_messages ch)) \<rparr>         
       
"

definition port_get_messages :: "Sys_Config \<Rightarrow> communication  \<Rightarrow> port_id \<Rightarrow> Message multiset"
where
"port_get_messages cnf c p_id \<equiv>
   let ch_id = port_channel cnf c p_id;
        ch = the ((chans c) ch_id) in               
      channel_get_messages ch
"             

definition port_full :: "Sys_Config \<Rightarrow> communication \<Rightarrow> port_id \<Rightarrow> bool"
where
"port_full cnf c p_id \<equiv>
    let ch_id = port_channel cnf c p_id in
       channel_full cnf c ch_id
"

definition port_empty :: "Sys_Config \<Rightarrow>  communication \<Rightarrow> port_id \<Rightarrow> bool"
where
"port_empty cnf c p_id \<equiv>
    let ch_id = port_channel cnf c p_id in       
       channel_empty c ch_id
"

definition set_que_aux :: "Sys_Config \<Rightarrow> communication \<Rightarrow> port_id \<Rightarrow> 
                              (channel_id \<Rightarrow> Message multiset) \<Rightarrow> Message multiset \<Rightarrow> 
                              (channel_id \<Rightarrow> Message multiset)"
where
"set_que_aux cnf c  p_id aux m \<equiv>
  let ch_id = port_channel cnf c p_id in 
    aux(ch_id:= m)
"

definition get_que_aux :: "Sys_Config \<Rightarrow> communication \<Rightarrow> port_id \<Rightarrow> (channel_id \<Rightarrow> Message multiset) \<Rightarrow> 
                             Message multiset"
where
"get_que_aux cnf c p_id aux \<equiv>
  let ch_id = port_channel cnf c p_id in 
    (aux ch_id)
"

definition port_max_size::"Sys_Config \<Rightarrow> communication \<Rightarrow> port_id \<Rightarrow> nat "
  where
    "port_max_size cnf com p_id \<equiv> channel_msg_size (get_channel cnf (port_channel cnf com p_id))"
    
definition port_get_msg_tim::"Sys_Config \<Rightarrow> communication \<Rightarrow> port_id \<Rightarrow> timer "
    where
    "port_get_msg_tim cnf com p_id \<equiv> 
    chan_msg_get_time (the (chans com (port_channel cnf com p_id)))"    
    
definition port_refresh_tim::"Sys_Config \<Rightarrow> communication \<Rightarrow> port_id \<Rightarrow> timer "
    where
    "port_refresh_tim cnf com p_id \<equiv> timer (the (ports com (port_id_name com p_id)))"
 
definition fresh_port_id::"communication \<Rightarrow> port_id"    
  where
   "fresh_port_id com \<equiv> SOME p_id. \<nexists>p. port_exists com p \<and> 
                                     (\<exists>pid. portid (the ((ports com) p)) = Some pid) \<and> 
                                     portid (the ((ports com) p)) = Some p_id"
      
subsection {* Scheduler abstraction *}

definition current ::"scheduler \<Rightarrow> partition_id"
where
"current sch \<equiv> sch"

                                                                                         
subsection {* Lemmas about removing messages *}

definition conf_wit :: Sys_Config
where 
"conf_wit \<equiv> \<lparr> partconf = {}, 
                        commconf = \<lparr> ports_conf = {}, channels_conf = {}\<rparr>,
                        procs = 1
                       \<rparr>" 

consts conf :: "Sys_Config"
                     
specification (conf) 
  n_n: "procs conf > 0"
  port_id_diff:"\<forall>p1 p2. p1\<noteq>p2 \<and> 
                        p1 \<in> ports_conf (commconf conf) \<and> p2 \<in> ports_conf (commconf conf) \<longrightarrow> 
                       port_name p1 \<noteq> port_name p2"
  ch_id_diff: "\<forall>ch1 ch2. ch1\<noteq>ch2 \<and> 
                        ch1 \<in> channels_conf (commconf conf) \<and> ch2 \<in> channels_conf (commconf conf) \<longrightarrow> 
                  channel_id ch1 \<noteq> channel_id ch2"
  part_id_diff: "\<forall>p1 p2. p1\<noteq>p2 \<and> 
                        p1\<in>partconf conf \<and> p2\<in>partconf conf \<longrightarrow>
                   part_id p1\<noteq>part_id p2 \<and> part_name p1 \<noteq> part_name p2 \<and>
                   part_ports p1 \<inter> part_ports p2 ={}" 
  scdests_not_emp: "\<forall>ch\<in>(channels_conf (commconf conf)). 
                      channel_destination ch \<noteq>{}" 
  src_not_dest: "\<forall>ch\<in>(channels_conf (commconf conf)). 
                   channel_valid_ports ch "
  port_disj: "\<forall>ch1 ch2. ch1\<noteq>ch2 \<and> ch1\<in>(channels_conf (commconf conf)) \<and> 
                        ch2\<in>(channels_conf (commconf conf)) \<longrightarrow>
                           channel_ports ch1 \<inter> channel_ports ch2 = {}"
  no_disconn_port:"\<forall>p\<in>ports_conf (commconf conf). 
                     \<exists>ch\<in>(channels_conf (commconf conf)).
                        port_name p\<in>channel_ports ch"
  no_disconn_ch: "\<forall>ch\<in>channels_conf (commconf conf). 
                    \<forall>p_id \<in> channel_ports ch.
                      \<exists>p\<in>(ports_conf (commconf conf)).
                        port_name p=p_id"
  no_disconn_part:"\<forall>part\<in>(partconf conf).   
                     \<forall>p_name\<in>part_ports part.                  
                        \<exists>p\<in>(ports_conf (commconf conf)).
                           port_name p= p_name"
  same_type:"\<forall>ch\<in>(channels_conf (commconf conf)). 
               \<forall>p_id \<in> channel_ports ch.                  
                 channel_queuing ch = port_queuing (get_port conf p_id)"
  same_direction_source:"\<forall>ch\<in>(channels_conf (commconf conf)).                     
                           port_dir (get_port conf (channel_source ch)) = SOURCE"
  same_direction_destination:"\<forall>ch\<in>(channels_conf (commconf conf)). 
                                 \<forall>p_id \<in> channel_destination ch. 
                                   port_dir (get_port conf p_id) = DESTINATION"  
  finite_conf_ports:"finite (ports_conf (commconf conf))"
  finite_conf_channels:"finite (channels_conf (commconf conf))"
  finite_conf_parts:"finite (partconf conf)"
  apply (rule exI[of _ conf_wit])   
  by (simp add: conf_wit_def)
        

   
definition state_conf :: "'b vars_scheme \<Rightarrow> bool"
where
"state_conf s \<equiv>
   (\<forall>ch\<in>(channels_conf (commconf conf)). 
     \<exists>ch_s. chans (communication_' s) (channel_id ch) = Some ch_s \<and>                               
                  channel_queuing ch = chan_queuing  ch_s) \<and>
    (\<forall>p \<in> (ports_conf (commconf conf)). port_exists (communication_' s) (port_name p)) \<and>
    (\<forall>p_n. port_exists (communication_' s) p_n \<longrightarrow> (\<exists>p. p\<in>(ports_conf (commconf conf)) \<and> port_name p = p_n )) \<and>    
     (\<forall>p_id p1 p2.
        port_exists (communication_' s) p1 \<and> port_exists (communication_' s) p2 \<and>  
        portid (the (ports (communication_' s) p1)) = Some p_id \<and>
        portid (the (ports (communication_' s) p2)) = Some p_id \<longrightarrow>  
        p1=p2)  \<and>
    procs conf = length (locals_' s) 
"

definition state_conf1 :: "'b vars_scheme \<Rightarrow> Port set \<Rightarrow> bool"
where
"state_conf1 s pts \<equiv>
   
    (\<forall>p \<in> pts. port_exists (communication_' s) (port_name p)) \<and>
    (\<forall>p_n. port_exists (communication_' s) p_n \<longrightarrow> (\<exists>p. p\<in>pts \<and> port_name p = p_n )) \<and>    
     (\<forall>p_id p1 p2.
        port_exists (communication_' s) p1 \<and> port_exists (communication_' s) p2 \<and>  
        portid (the (ports (communication_' s) p1)) = Some p_id \<and>
        portid (the (ports (communication_' s) p2)) = Some p_id \<longrightarrow>  
        p1=p2)  
"

(* We establish these lemmas after we define the specification *)
    
lemma unique_port_conf_state: "x\<in>pts \<Longrightarrow>
       state_conf1 s pts \<Longrightarrow>
       \<exists>!p_name. port_name x = p_name \<and> port_exists (communication_' s) p_name"  
  unfolding state_conf1_def port_exists_def
  by auto
    
lemma unique_port_conf_name_state: 
"x\<in>pts \<Longrightarrow>
 y\<in>pts \<Longrightarrow>
 port_name x = port_name y \<Longrightarrow>
 \<forall>p1 p2. p1\<noteq>p2 \<and> 
        p1 \<in>pts \<and> p2 \<in> pts \<longrightarrow> 
       port_name p1 \<noteq> port_name p2 \<Longrightarrow>
 x=y"
  by auto

lemma dom_ports_names_conf:
  "state_conf s \<Longrightarrow>
   dom (ports (communication_' s)) = 
   (port_name `  (ports_conf (commconf conf)))"
  unfolding state_conf_def dom_def
  using port_exists_def by blast
    
lemma finite_ports: 
"state_conf s \<Longrightarrow>
 finite  (dom (ports (communication_' s)))"
 by (auto  dest: dom_ports_names_conf simp  add: finite_conf_ports )

lemma finite_ids:
"state_conf s \<Longrightarrow>
finite {n.  (\<exists>x. (ports (communication_' s)) n = Some x)}"
by (auto simp add: dom_def dest: finite_ports)

    
 lemma finite_pids:
 assumes a0: "state_conf s" 
 shows "finite ( {pid. (port_open (communication_' s) pid)})"
 proof-
   have eq_set: 
     "{pid. port_open (communication_' s) pid} = 
      {pid. (\<exists>n y p_id p. (ports (communication_' s)) n = Some y \<and> 
                         p = the ((ports (communication_' s)) n) \<and> 
                         (portid p = Some p_id) \<and> pid=the (portid p))}
       "
   unfolding port_open_def port_exists_def
   by auto
  thus  ?thesis  
  using a0 by (auto dest: finite_ids) 
qed   
   
lemma fresh_port_pids:"state_conf s\<Longrightarrow> 
       \<exists>z. z\<notin>{pid. (port_open (communication_' s) pid)}"
  using ex_new_if_finite finite_pids by fastforce

    
lemma port_open_port_exists:
   "port_open c p_id \<Longrightarrow>
    \<exists>p. port_exists c p"
  unfolding port_open_def port_exists_def
  by auto
   
lemma port_open_port_name_unique:
  assumes a0:"state_conf s" and       
       a1:"port_open (communication_' s) p_id" and
       a2:"port_exists (communication_' s) p_n1 \<and> portid (the ((ports (communication_' s)) p_n1)) = Some p_id" and
       a3:"port_exists (communication_' s) p_n2 \<and> portid (the ((ports (communication_' s)) p_n2)) = Some p_id" 
     shows "p_n1 = p_n2"
 using a0 a1 a2 a3
  unfolding state_conf_def port_open_def port_exists_def by auto
    
lemma port_name_open_unique:
  "state_conf s \<Longrightarrow>
    port_open (communication_' s) p_id \<Longrightarrow>
   \<exists>!p_n. port_exists (communication_' s) p_n \<and> portid (the ((ports (communication_' s)) p_n)) = Some p_id"
  unfolding port_open_def state_conf_def by auto
    
lemma port_id_name_port: 
assumes a0:"state_conf s" and       
     a1:"port_open (communication_' s) p_id" and
     a2:"pn = port_id_name (communication_' s) p_id"
   shows "port_exists (communication_' s) pn \<and> portid (the ((ports (communication_' s)) pn)) = Some p_id"
proof-
  obtain pn' where pe:"port_exists (communication_' s) pn' \<and> portid (the ((ports (communication_' s)) pn')) =Some p_id"  
    using a1 unfolding port_open_def by auto
  moreover have "\<exists>!p_n. port_exists (communication_' s) p_n \<and> portid (the ((ports (communication_' s)) p_n)) = Some p_id"
    using port_name_open_unique[OF a0 a1] by auto  
  thus ?thesis  
  using the_equality[of _ pn'] a2 pe unfolding port_id_name_def
  by (metis (mono_tags, lifting) ) 
   
qed   
  
lemma port_open_port_conf:
  "state_conf s \<Longrightarrow>
    port_open (communication_' s) p_id \<Longrightarrow>
   \<exists>p. p\<in> (ports_conf (commconf conf)) \<and> port_name p = port_id_name (communication_' s) p_id"  
  using port_id_name_port  
  unfolding state_conf_def port_exists_def 
  by blast
    
lemma port_open_unique_port_conf:
  "state_conf s \<Longrightarrow>
    port_open (communication_' s) p_id \<Longrightarrow>
   \<exists>!p. p\<in> (ports_conf (commconf conf)) \<and> port_name p = port_id_name (communication_' s) p_id"  
  using port_open_port_conf  port_id_diff
  unfolding state_conf_def
   apply auto
   by (metis (full_types))
    
lemma port_diff_port_name_diff:
  assumes a0:"state_conf s" and       
       a1:"port_open (communication_' s) p_id1" and
       a2:"port_open (communication_' s) p_id2" and
      a3:"pn1 = port_id_name (communication_' s) p_id1" and
      a4:"pn2 = port_id_name (communication_' s) p_id2" and
      a5:"p_id1 \<noteq> p_id2"
    shows "pn1 \<noteq> pn2"
  using a0 a1 a2 a3 a4 a5     
  by (metis  option.inject port_id_name_port)

lemma port_eq_port_name_eq:
  assumes
      a0:"pn1 = port_id_name (communication_' s) p_id" and
      a1:"pn2 = port_id_name (communication_' s) p_id"       
    shows "pn1 = pn2"
      using a0 a1
by auto    

lemma port_in_part_ex_port_unique:
  assumes a0:"state_conf s" and
       a1:"port_id_in_part conf (communication_' s) pa_id p_id" and
       a2:"port_id_in_part conf (communication_' s) pa_id1 p_id" and
       a3:"port_open (communication_' s) p_id"   
     shows   "pa_id1 = pa_id"
   using a0 a1 a2 a3  part_id_diff
   by (metis insert_disjoint(1) mk_disjoint_insert port_id_in_part_def)

lemma port_in_part_port_exists: "state_conf s \<Longrightarrow>
       port_in_part conf p_id port_n \<Longrightarrow>
       port_exists (communication_' s) port_n"
  unfolding port_in_part_def port_exists_def state_conf_def
  using no_disconn_part port_exists_def  by fastforce

lemma exist_only_one_channel: 
  assumes a0:"state_conf s" and
   a1:"port_open (communication_' s) p_id" 
 shows  
   "\<exists>!ch\<in>(channels_conf (commconf conf)). 
      port_id_name (communication_' s) p_id\<in>channel_ports ch"
using port_open_unique_port_conf
 proof-
  have " \<exists>!p_n. port_exists (communication_' s) p_n \<and> portid (the ((ports (communication_' s)) p_n)) =Some p_id"  
    using a0 a1
    by (simp add: port_name_open_unique)
  then obtain p_n where 
      "portid(the ((ports (communication_' s)) p_n)) = Some p_id \<and>
        (\<forall>p_n1. port_exists (communication_' s) p_n1 \<and> portid(the ((ports (communication_' s)) p_n1)) = Some p_id \<longrightarrow> 
         p_n1 = p_n)"
  by auto
  moreover obtain p where 
    "p\<in>(ports_conf (commconf conf)) \<and> port_name p = p_n"
    using a0 a1 calculation  unfolding state_conf_def port_exists_def 
    by (metis a0 port_id_name_port port_open_unique_port_conf)
  moreover have p_id_name:"port_id_name (communication_' s) p_id = p_n"
    using a1 calculation 
    unfolding port_open_def port_id_name_def by auto
  moreover have "\<forall>p1\<in>(ports_conf (commconf conf)). p1\<noteq>p\<longrightarrow> port_name p1\<noteq>p_n"
    using port_id_diff a0 calculation
    by metis 
  ultimately obtain ch where "p_n \<in> channel_ports ch \<and> 
                        ch \<in> channels_conf (commconf conf)"
    using no_disconn_port by blast
  thus ?thesis using p_id_name  port_disj
    by blast 
qed
    
  
lemma exist_only_one_channel_id: 
  assumes a0:"state_conf s" and
   a1:"port_open (communication_' s) p_id" 
 shows "\<exists>!ch_id. \<exists>ch chc. 
         chans (communication_' s) ch_id = Some ch \<and> 
         channel_id chc = ch_id \<and> chc \<in> channels_conf (commconf conf) \<and>
         port_id_name (communication_' s) p_id \<in>channel_ports chc" 
  using exist_only_one_channel[OF a0 a1] using a0
    unfolding state_conf_def
  by metis   

 

lemma only_ch_id:
"ch_id =  channel_id ch' \<and>
 ch_id' = channel_id ch' \<Longrightarrow>
 ch_id = ch_id'"
by auto
        
lemma only_ch_ch_id:
      "ch\<in>(channels_conf (commconf conf)) \<Longrightarrow>
       ch_id =  channel_id ch \<Longrightarrow>
       ch = (THE ch. (ch\<in> (channels_conf (commconf conf))) \<and> channel_id ch = ch_id)"
by (metis (mono_tags, lifting) ch_id_diff the_equality) 
   
 
lemma exist_port_in_channel: 
  "state_conf s \<Longrightarrow>
   port_open (communication_' s) p_id \<Longrightarrow>
   \<exists>ch_id.  port_in_channel conf  (communication_' s) p_id ch_id" 
 unfolding port_in_channel_def get_channel_def port_name_in_channel_def
   by (metis (full_types) exist_only_one_channel)

lemma exist_only_one_quechannel: 
  assumes a0:"state_conf s \<and>
              port_open (communication_' s) p_id \<and>
              port_in_channel conf (communication_' s) p_id ch_id1 \<and> 
              port_in_channel conf (communication_' s) p_id ch_id2"
  shows   "ch_id1 = ch_id2"
  using a0 exist_only_one_channel 
  unfolding port_in_channel_def port_name_in_channel_def by auto


lemma exist_only_one_quechannel': 
  assumes a0:"state_conf s" and
          a1:"port_open (communication_' s) p_id" and 
          a2:"port_open (communication_' s) p_id'" and
          a3:"port_in_channel conf  (communication_' s) p_id c1" and
          a4:"port_in_channel conf  (communication_' s) p_id' c1"
        shows   "port_in_channel conf (communication_' s) p_id = 
                 port_in_channel conf (communication_' s) p_id'"
  using  exist_only_one_quechannel a0 a1 a2 a3 a4 by blast  

lemma port_exist_unique_channel:
 "state_conf s \<Longrightarrow>
   port_open (communication_' s) p_id \<Longrightarrow>      
   \<exists>!ch_id. port_in_channel conf (communication_' s) p_id ch_id"
using exist_only_one_quechannel exist_port_in_channel
by auto

lemma port_channel_get_channel:
assumes a0:"state_conf  s" and
        a1:" port_open (communication_' s) p_id" and
        a2:"port_channel conf (communication_' s) p_id = ch_id" and
        a3: "(get_channel conf ch_id) = ch" 
shows "ch \<in> channels_conf (commconf conf) \<and>
      channel_id ch = ch_id"
proof - 
 obtain ch_id1 where "port_in_channel conf (communication_' s) p_id ch_id1 \<and>
     (\<forall>ch_id. port_in_channel conf (communication_' s) p_id ch_id \<longrightarrow>
        ch_id1 = ch_id) \<and> ch_id = ch_id1" 
   using port_exist_unique_channel[OF a0 a1]  a2 the_equality 
   unfolding port_channel_def by blast 
 then show ?thesis
   using a3 only_ch_ch_id
   unfolding get_channel_def  port_in_channel_def port_name_in_channel_def
   by fast
qed

lemma port_in_channel_get_channel:
assumes a0:"port_in_channel conf (communication_' s) p_id ch_id" and
        a1: "(get_channel conf ch_id) = ch" 
shows "ch \<in> channels_conf (commconf conf) \<and>
      channel_id ch = ch_id"
proof - 
 obtain ch_id1 where "port_in_channel conf (communication_' s) p_id ch_id1 \<and>
     (\<forall>ch_id. port_in_channel conf (communication_' s) p_id ch_id \<longrightarrow>
        ch_id1 = ch_id) \<and> ch_id = ch_id1" 
   using  a0 
   unfolding port_in_channel_def port_name_in_channel_def
   by (metis disjoint_iff_not_equal port_disj)
 then show ?thesis
   using a1 only_ch_ch_id
   unfolding get_channel_def  port_in_channel_def port_name_in_channel_def
   by fastforce
qed


lemma port_channel:"
   state_conf s \<Longrightarrow>
   port_open (communication_' s) p_id \<Longrightarrow>
   port_in_channel conf (communication_' s) p_id ch \<Longrightarrow> 
   port_channel conf (communication_' s) p_id = ch"
unfolding port_channel_def 
using  exist_only_one_quechannel
by blast

lemma port_in_channel_eq_port_channel:"
   state_conf s \<Longrightarrow>
   port_open (communication_' s) p_id \<Longrightarrow>
   port_in_channel conf (communication_' s) p_id ch \<Longrightarrow> 
   port_channel conf (communication_' s) p_id = ch1 \<Longrightarrow>
   ch = ch1"
unfolding port_channel_def 
using port_channel port_channel_def by blast
  
  
  
lemma port_unique_channel:
"state_conf s \<Longrightarrow>
port_open (communication_' s) p_id \<Longrightarrow>             
 \<exists>!ch_id. port_in_channel conf (communication_' s) p_id ch_id \<and> 
    port_channel conf (communication_' s) p_id = ch_id"
using port_exist_unique_channel port_channel 
  by blast
    
lemma port_channel_exists_channel:"port_in_channel conf (communication_' s) p_id ch_id \<Longrightarrow>
       \<exists>ch. (ch\<in> (channels_conf (commconf conf))) \<and> channel_id ch = ch_id"    
  unfolding state_conf_def port_in_channel_def port_name_in_channel_def port_id_name_def
    port_open_def port_exists_def
  by auto
    
lemma port_channel_channel_id:"port_in_channel conf (communication_' s) p_id ch_id \<Longrightarrow>
        (ch1\<in> (channels_conf (commconf conf))) \<and> channel_id ch1 = ch_id \<Longrightarrow>
        (ch2\<in> (channels_conf (commconf conf))) \<and> channel_id ch2 = ch_id \<Longrightarrow>
       ch1 = ch2"   
  unfolding port_in_channel_def port_name_in_channel_def
  using ch_id_diff by fastforce
    
lemma port_in_channel_unique_channel:
  "port_in_channel conf (communication_' s) p_id ch_id \<Longrightarrow>
  \<exists>!ch. ch\<in>(channels_conf (commconf conf)) \<and> channel_id ch = ch_id"
  using port_channel_channel_id port_channel_exists_channel
  by blast

lemma port_open_channel_unique_channel:
  "state_conf s \<Longrightarrow>
   port_open (communication_' s) p_id \<Longrightarrow>   
  \<exists>!ch. ch\<in>(channels_conf (commconf conf)) \<and> 
        channel_id ch = port_channel conf (communication_' s) p_id"  
  using ch_id_diff port_channel_def port_channel_get_channel by fastforce        
    
lemma port_max_size_port:
 assumes a0: "state_conf s " and
         a1: "port_open (communication_' s) p_id"
 shows
  "\<exists>!ch. \<exists>n. channel_msg_size ch = n \<and> 
        ch\<in> (channels_conf (commconf conf)) \<and>
       channel_id ch = port_channel conf (communication_' s) p_id \<and> 
       n = port_max_size conf (communication_' s) p_id"
unfolding port_max_size_def get_channel_def
using port_open_channel_unique_channel[OF a0 a1] only_ch_ch_id by fastforce

  
lemma queuing_or_sampling_port:
 "port_sampling p \<or> port_queuing p"
by (cases p, auto)

lemma queuing_or_sampling_channel:
 "channel_sampling c \<or> channel_queuing c"
by (cases c, auto)

lemma queuing_or_sampling_chan:
 "chan_sampling c \<or> chan_queuing c"
unfolding chan_sampling_def chan_queuing_def
  by auto
    
lemma not_ch_queuing_sampling:
  "ch_id_queuing conf ch \<and> ch_id_sampling conf ch \<Longrightarrow>
   False"
  unfolding ch_id_queuing_def ch_id_sampling_def 
    using ch_id_diff
    by (metis no_c_sampling_queuing)
 
lemma not_p_queing_sampling:
  "p_queuing conf (communication_' s) p_id \<Longrightarrow>
   \<not> p_sampling conf (communication_' s) p_id"
  unfolding p_queuing_def p_sampling_def 
  using not_ch_queuing_sampling by auto
 
lemma not_p_queing_sampling':
  " p_sampling conf (communication_' s) p_id \<Longrightarrow>
   \<not> p_queuing conf (communication_' s) p_id "
  unfolding p_queuing_def p_sampling_def 
  using not_ch_queuing_sampling by auto    
    
lemma p_queuing_port_queuing:"state_conf s \<Longrightarrow>
      port_open (communication_' s) p_id \<Longrightarrow>
      p_queuing conf (communication_' s) p_id \<Longrightarrow> 
      \<exists>p. (p\<in> (ports_conf (commconf conf))) \<and> 
      port_id_name (communication_' s) p_id  = port_name p \<and> 
      port_queuing p
"
proof -
  assume a0: "state_conf s" and
         a1:"port_open (communication_' s) p_id" and
         a2:" p_queuing conf (communication_' s) p_id"
  then obtain ch_id ch where ch:"(ch\<in> (channels_conf (commconf conf))) \<and> channel_id ch = ch_id \<and>  
              channel_queuing ch \<and> port_id_name (communication_' s) p_id\<in> channel_ports ch"
    using a2  ch_id_diff port_unique_channel
    unfolding p_queuing_def ch_id_queuing_def port_in_channel_def  port_name_in_channel_def
    by metis
  then obtain p where p:"(p\<in> (ports_conf (commconf conf))) \<and> 
     port_name p = port_id_name (communication_' s) p_id"
    using no_disconn_ch by fastforce
  then have "p=get_port conf (port_id_name (communication_' s) p_id)" 
    unfolding get_port_def port_eq_port_name_eq using port_id_diff 
    the_equality[of "\<lambda>p.  (p\<in> (ports_conf (commconf conf))) \<and> port_name p = port_id_name (communication_' s) p_id"  p]
    by (metis (no_types, lifting) )
  then show ?thesis using same_type ch p
    by auto
qed 

lemma p_sampling_port_sampling:"state_conf s \<Longrightarrow>
      port_open (communication_' s) p_id \<Longrightarrow>
      p_sampling conf (communication_' s) p_id \<Longrightarrow> 
      \<exists>p. (p\<in> (ports_conf (commconf conf))) \<and> 
      port_id_name (communication_' s) p_id  = port_name p \<and> 
      port_sampling p
"
proof -
  assume a0: "state_conf s" and
         a1:"port_open (communication_' s) p_id" and
         a2:" p_sampling conf (communication_' s) p_id"
  then obtain ch_id ch where ch:"(ch\<in> (channels_conf (commconf conf))) \<and> channel_id ch = ch_id \<and>  
              channel_sampling ch \<and> port_id_name (communication_' s) p_id\<in> channel_ports ch"
    using a2  ch_id_diff port_unique_channel
    unfolding p_sampling_def ch_id_sampling_def port_in_channel_def  port_name_in_channel_def
    by metis
  then obtain p where p:"(p\<in> (ports_conf (commconf conf))) \<and> 
     port_name p = port_id_name (communication_' s) p_id"
    using no_disconn_ch by fastforce
  then have "p=get_port conf (port_id_name (communication_' s) p_id)" 
    unfolding get_port_def port_eq_port_name_eq using port_id_diff 
    the_equality[of "\<lambda>p.  (p\<in> (ports_conf (commconf conf))) \<and> port_name p = port_id_name (communication_' s) p_id"  p]
    by (metis (no_types, lifting) )
  then show ?thesis using same_type ch p
     no_c_sampling_queuing queuing_or_sampling_port by fastforce
    
qed   
    

lemma p_queuing_ch_id_queuing:
     "state_conf s \<Longrightarrow>
      port_open (communication_' s) p_id \<Longrightarrow>
      p_queuing conf (communication_' s) p_id \<Longrightarrow> 
      port_in_channel conf (communication_' s) p_id ch_id \<Longrightarrow>      
      ch_id_queuing conf ch_id
"
  using port_channel unfolding p_queuing_def by auto
  
lemma p_queuing_ch_id_queuing':
 "state_conf s \<Longrightarrow>
   port_open (communication_' s) p_id \<Longrightarrow>
   p_queuing conf (communication_' s) p_id \<Longrightarrow>
   ch_id_queuing conf (port_channel conf (communication_' s) p_id)"
  using port_channel 
  unfolding p_queuing_def  by auto   

lemma p_sampling_ch_id_sampling:
     "state_conf s \<Longrightarrow>
      port_open (communication_' s) p_id \<Longrightarrow>      
      p_sampling conf (communication_' s) p_id \<Longrightarrow> 
      port_in_channel conf (communication_' s)  p_id ch_id \<Longrightarrow>      
      ch_id_sampling conf ch_id
"
  using port_channel unfolding p_sampling_def by auto
    
 lemma p_sampling_ch_id_sampling':
     "state_conf s \<Longrightarrow>
      port_open (communication_' s) p_id \<Longrightarrow>      
      p_sampling conf (communication_' s) p_id \<Longrightarrow>       
      ch_id_sampling conf (port_channel conf (communication_' s) p_id)
"
using port_channel unfolding p_sampling_def by auto

lemma p_queuing_chan_queuing:
  assumes a0:"state_conf s" and 
         a0':" port_open (communication_' s) p_id" and
         a1: "p_queuing conf  (communication_' s) p_id" and
         a2: "port_in_channel conf (communication_' s) p_id ch_id"          
       shows   "\<exists>chan. chans (communication_' s) ch_id = Some chan \<and> 
                   chan_queuing chan"
 using p_queuing_ch_id_queuing[OF a0 a0' a1 a2] a0 
  unfolding ch_id_queuing_def state_conf_def by auto
    
lemma p_sampling_chan_sampling:
 assumes a0:"state_conf s" and 
         a0':" port_open (communication_' s) p_id" and
         a1: "p_sampling conf  (communication_' s) p_id" and
         a2: "port_in_channel conf  (communication_' s) p_id ch_id"          
 shows   "\<exists>chan. chans (communication_' s) ch_id = Some chan \<and> chan_sampling chan"
 using p_sampling_ch_id_sampling[OF a0 a0' a1 a2] a0 
 unfolding ch_id_sampling_def state_conf_def
  using no_c_sampling_queuing queuing_or_sampling_chan by blast
    
lemma p_chan:
 assumes a0:"state_conf s" and 
         a0':" port_open (communication_' s) p_id" and         
         a2: "port_in_channel conf  (communication_' s) p_id ch_id"          
       shows   "\<exists>chan. chans (communication_' s) ch_id = Some chan" 
  using a0 a2 port_in_channel_get_channel state_conf_def by fastforce

lemma ch_id_queuing:
"state_conf x \<Longrightarrow>
 chans (communication_' y) ch_id = Some ch' \<and> ch_id_queuing conf ch_id \<Longrightarrow> 
  \<exists>ch'. chans (communication_' x) ch_id = Some ch' \<and> ch_id_queuing conf ch_id"
  unfolding state_conf_def ch_id_queuing_def chan_queuing_def chan_sampling_def
  by blast   
 
lemma p_queuing_channel:
   "port_channel conf (communication_' x) p_id = 
    port_channel conf (communication_' y) p_id \<Longrightarrow>
    p_queuing conf (communication_' x) p_id =
    p_queuing conf (communication_' y) p_id"    
  unfolding p_queuing_def by auto 
(* lemma p_queuing_a_que_aux:
 assumes a0:"state_conf x" and
         a1: "p_queuing conf p_id" and
         a2: "port_in_channel conf p_id ch_id"          
 shows   "\<exists>ms. (a_que_aux (locals_' x!i)) ch_id =  ms"
 using p_queuing_ch_id_queuing[OF a1 a2] a0 
 unfolding ch_id_queuing_def state_conf_def by auto

lemma p_queuing_r_que_aux:
 assumes a0:"state_conf x" and
         a1: "p_queuing conf p_id" and
         a2: "port_in_channel conf p_id ch_id"          
 shows   "\<exists>ms. (r_que_aux (locals_' x!i)) ch_id =  ms"
 using p_queuing_ch_id_queuing[OF a1 a2] a0 
 unfolding ch_id_queuing_def state_conf_def by auto    
*)
lemma port_not_full_channel_not_full:
   "state_conf s \<Longrightarrow>
     port_open (communication_' s) p_id \<Longrightarrow>  
  \<not> port_full conf (communication_' s) p_id \<Longrightarrow> 
   port_in_channel conf  (communication_' s) p_id ch_id \<Longrightarrow>
 \<not> channel_full conf (communication_' s) ch_id"
unfolding port_full_def  port_channel
by auto

lemma queuing_remove:
      "channel_get_messages (channel_remove_message ch m) =
         channel_get_messages ch - {# m #}"
unfolding channel_get_messages_def channel_remove_message_def channel_set_messages_def
by (cases "data ch",auto simp add: diff_single_trivial option.case_eq_if)



lemma port_buffer_remove:
  "port_get_messages conf (port_remove_message conf (communication_' s) p_id m) p_id =
   (port_get_messages conf  (communication_' s) p_id) -{# m #}"
using queuing_remove
unfolding port_get_messages_def port_remove_message_def 
          port_in_channel_def port_channel_def port_name_in_channel_def          
          Let_def   port_id_name_def port_exists_def 
  by auto

lemma eq_port_messages_same_data:"port_get_messages conf c pt_id = port_get_messages conf c' pt_id \<Longrightarrow>
      chans c (port_channel conf c pt_id) = Some ch \<and> chan_queuing ch \<Longrightarrow>
      chans c' (port_channel conf c' pt_id) = Some ch' \<and> chan_queuing ch' \<Longrightarrow>
      data (the (chans c (port_channel conf c pt_id))) = 
        data (the (chans c' (port_channel conf c' pt_id)))"
  unfolding port_get_messages_def Let_def channel_get_messages_def chan_queuing_def chan_sampling_def
  apply auto
  apply (case_tac "data ch") apply auto
  by (metis Channel_data.exhaust Channel_data.simps(5) Channel_data.simps(6))
  
lemma get_port_name_unfold:
 "state_conf s \<Longrightarrow>
  \<exists>p. p\<in> (ports_conf (commconf conf)) \<and> port_name p = p_name \<Longrightarrow> 
  get_port conf p_name = p \<Longrightarrow>
  (p\<in> (ports_conf (commconf conf))) \<and> port_name p =  p_name"
  using port_id_diff the_equality  unfolding get_port_def state_conf_def
    by (metis (mono_tags, lifting))   
    
lemma get_port_unfold:
 "state_conf s \<Longrightarrow>
 port_open (communication_' s) p_id \<Longrightarrow> 
  get_port conf (port_id_name (communication_' s) p_id) = p \<Longrightarrow>
  (p\<in> (ports_conf (commconf conf))) \<and> port_name p = 
      port_id_name (communication_' s) p_id"
  using get_port_name_unfold port_open_unique_port_conf by fast  
    

lemma not_port_empty_size_messages_not_zero:
" \<not> port_empty conf com p_id \<Longrightarrow>
   size (port_get_messages conf com p_id ) > 0
"
  unfolding  port_empty_def channel_empty_def
             channel_get_bufsize_def  port_get_messages_def 
  by (simp add: nonempty_has_size)  
    
lemma port_max_size:"state_conf s \<Longrightarrow>
       port_open (communication_' s) p_id \<Longrightarrow>
       \<exists>!n. n = port_max_size conf (communication_' s) p_id"
  by auto


lemma not_port_empty_buffer_elem:
"\<not> port_empty conf com p \<Longrightarrow> 
    \<exists>x. x \<in># port_get_messages conf com p
" 
using not_port_empty_size_messages_not_zero
by (metis Suc_pred size_eq_Suc_imp_elem) 

lemma not_port_empty_get_some_message:
"\<not> port_empty conf com p_id \<Longrightarrow> 
  \<exists>m.  port_get_message conf com p_id = Some m
"
by (simp add: channel_empty_def channel_get_bufsize_def port_empty_def port_get_message_def)

lemma insert_message_inc_buf_size:        
"chan_queuing ch \<Longrightarrow>
 channel_get_bufsize (channel_insert_message ch m t)
 = (channel_get_bufsize ch) + 1"
unfolding channel_get_bufsize_def channel_insert_message_def 
          channel_set_messages_def channel_get_messages_def 
          chan_queuing_def chan_sampling_def
  by (cases "data ch", auto)
    
lemma remove_message_less_eq_buf_size:        
"chan_queuing ch \<Longrightarrow>
 channel_get_bufsize (channel_remove_message ch m)
 \<le> (channel_get_bufsize ch)"
unfolding channel_get_bufsize_def channel_remove_message_def 
          channel_set_messages_def channel_get_messages_def 
          chan_queuing_def chan_sampling_def
 by (cases "data ch", auto simp add: size_mset_mono)
 



lemma insert_message_sampchannel:        
"chan_sampling ch \<Longrightarrow>
 channel_get_bufsize (channel_insert_message ch m t)
 = 1"
unfolding  channel_get_bufsize_def channel_insert_message_def 
          channel_set_messages_def channel_get_messages_def 
          chan_sampling_def                
by (cases "data ch", auto)

lemma not_sampport_full_size:
" channel_sampling ch \<Longrightarrow>
  (ch\<in> (channels_conf (commconf conf))) \<and> channel_id ch = ch_id \<Longrightarrow>
  state_conf s \<Longrightarrow>
  size (channel_get_messages (channel_insert_message (the (chans (communication_' s) ch_id)) m t)) \<le>
  channel_size ch                
 "
proof -
  assume a0:" channel_sampling ch" and
         a1:" (ch\<in> (channels_conf (commconf conf))) \<and> channel_id ch = ch_id" and
         a2:"state_conf  s"
   then have "channel_get_bufsize (channel_insert_message (the (chans (communication_' s) ch_id)) m t) = 1"
     unfolding channel_get_bufsize_def state_conf_def 
     using a0 One_nat_def a1 channel_get_bufsize_def channel_queuing.simps(1) insert_message_sampchannel queuing_or_sampling_chan
     by (metis no_c_sampling_queuing option.sel)              
   then show ?thesis 
   using a0 unfolding channel_get_bufsize_def
    by (cases ch, auto) 
qed
 
lemma queuing_insert_message:
  "chan_queuing ch \<Longrightarrow>
   (channel_get_messages ch) + {# m #} = 
     channel_get_messages (channel_insert_message ch m t)"  
  unfolding chan_queuing_def chan_sampling_def channel_get_messages_def channel_insert_message_def
            channel_set_messages_def
  by (cases "data ch", auto)

lemma queuing_port_insert:
  "state_conf s \<Longrightarrow>
   port_open (communication_' s) p_id \<Longrightarrow>
   p_queuing conf (communication_' s) p_id \<Longrightarrow>      
   port_get_messages conf (port_insert_message conf (communication_' s) p_id  m t) p_id =
   port_get_messages conf (communication_' s) p_id +{# m #}"
proof -
  assume a0: "state_conf s" and
         a1: " port_open (communication_' s) p_id" and
         a2: "p_queuing conf (communication_' s) p_id"         
  then have "\<exists>!ch_id. port_in_channel conf (communication_' s) p_id ch_id \<and> 
     port_channel conf (communication_' s) p_id = ch_id"
    using port_unique_channel by auto 
  then have "chan_queuing (the (chans (communication_' s) (port_channel conf (communication_' s) p_id)))"    
    using a0 a1 a2  p_queuing_chan_queuing by fastforce    
  then show ?thesis 
    using   queuing_insert_message 
    unfolding port_get_messages_def port_in_channel_def 
           Let_def  port_channel_def port_insert_message_def 
           port_exists_def  port_id_name_def           
    by auto
qed

lemma port_open_insert_queuing:
"state_conf s \<Longrightarrow>
   port_open (communication_' s) p_id \<Longrightarrow>     
   port_open (communication_' (s\<lparr>communication_' := (port_insert_message conf (communication_' s) p_id  m t)\<rparr>)) p_id"
proof-
assume a0: "state_conf s" and
       a1: "port_open (communication_' s) p_id" 
  then have "\<exists>!ch_id. port_in_channel conf (communication_' s) p_id ch_id \<and> 
     port_channel conf (communication_' s) p_id = ch_id"
    using port_unique_channel by auto
  then have "ports (communication_' s) = ports (communication_' (s\<lparr>communication_' := (port_insert_message conf (communication_' s) p_id  m t)\<rparr>))"
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

lemma port_open_insert_state_conf:
"state_conf s \<Longrightarrow>
   port_open (communication_' s) p_id \<Longrightarrow>     
   state_conf (s\<lparr>communication_' := (port_insert_message conf (communication_' s) p_id  m t)\<rparr>)"
proof-
assume a0: "state_conf s" and
       a1: "port_open (communication_' s) p_id" 
  then have "\<exists>!ch_id. port_in_channel conf (communication_' s) p_id ch_id \<and> 
     port_channel conf (communication_' s) p_id = ch_id"
    using port_unique_channel by auto
  
  thus ?thesis using a0  a1  unfolding state_conf_def channel_set_messages_def 
          channel_insert_message_def chan_queuing_def channel_get_messages_def
           Let_def   port_insert_message_def  port_in_channel_def chan_sampling_def
           port_exists_def  port_id_name_def  port_open_def  port_exists_def 
    apply (auto; case_tac "data (the (chans (communication_' s) (port_channel conf (communication_' s) p_id)))")
    by auto
qed

lemma insert_message_locals:
"locals_' (s\<lparr>communication_' := (port_insert_message conf (communication_' s) p_id  m t)\<rparr>) = locals_' s"
proof-
  show ?thesis unfolding state_conf_def channel_set_messages_def 
          channel_insert_message_def chan_queuing_def channel_get_messages_def
           Let_def   port_insert_message_def  port_in_channel_def chan_sampling_def
           port_exists_def  port_id_name_def  port_open_def  port_exists_def 
    by auto
qed

lemma insert_message_ports:
"ports (communication_' (s\<lparr>communication_' := (port_insert_message conf (communication_' s) p_id  m t)\<rparr>)) = 
 ports (communication_' s)"   
unfolding  port_insert_message_def Let_def
  by auto

lemma insert_message_ports':
"ports  (port_insert_message conf (communication_' s) p_id  m t) = 
 ports (communication_' s)"   
unfolding  port_insert_message_def Let_def
  by auto


lemma insert_message_port_mut:
  "ports_mut (communication_' (s\<lparr>communication_' := (port_insert_message conf (communication_' s) p_id  m t)\<rparr>)) = 
 ports_mut (communication_' s)"   
unfolding  port_insert_message_def Let_def
  by auto

lemma insert_message_port_mut':
  "ports_mut (port_insert_message conf (communication_' s) p_id  m t) = 
 ports_mut (communication_' s)"   
unfolding  port_insert_message_def Let_def
  by auto

lemma port_get_mutex_insert_message:"state_conf s \<Longrightarrow>
   port_open (communication_' s) p_id \<Longrightarrow>  
 port_get_mutex conf (port_insert_message conf (communication_' s) p_id m t) p_id =
  port_get_mutex conf (communication_' s) p_id"
 proof-
assume a0: "state_conf s" and
       a1: "port_open (communication_' s) p_id" 
  then have "\<exists>!ch_id. port_in_channel conf (communication_' s) p_id ch_id \<and> 
     port_channel conf (communication_' s) p_id = ch_id"
    using port_unique_channel by auto
  
  thus ?thesis using a0  a1  unfolding  channel_set_messages_def 
          channel_insert_message_def chan_queuing_def channel_get_messages_def
           Let_def   port_insert_message_def  port_in_channel_def chan_sampling_def
           port_exists_def  port_id_name_def  port_open_def  port_exists_def
port_get_mutex_def channel_get_mutex_def
    apply (auto; case_tac "data (the (chans (communication_' s) (port_channel conf (communication_' s) p_id)))")
    by (auto simp add: port_channel_def port_in_channel_def port_id_name_def port_exists_def)
qed
  


(* lemma insert_message_chan_mut:
  "state_conf s \<Longrightarrow>
   port_open (communication_' s) p_id \<Longrightarrow>  
 chans (communication_' (s\<lparr>communication_' := (port_insert_message conf (communication_' s) p_id  m t)\<rparr>)) = 
 chans (communication_' s)"   
unfolding  port_insert_message_def Let_def
  by auto *)


lemma sampling_insert_message:
  "chan_sampling ch \<Longrightarrow>   
     channel_get_messages (channel_insert_message ch m t) = {# m #}"  
unfolding chan_sampling_def 
         channel_get_messages_def channel_insert_message_def channel_set_messages_def
  by (cases "data ch", auto)

lemma sampling_port_insert:
  "state_conf s \<Longrightarrow>
   port_open (communication_' s) p_id \<Longrightarrow>
   p_sampling conf (communication_' s) p_id \<Longrightarrow> 
    port_get_messages conf (port_insert_message conf (communication_' s) p_id  m t) p_id =
    {# m #}"
proof -
 assume a0: "state_conf s" and
         a1: "port_open (communication_' s) p_id" and
         a2: "p_sampling conf (communication_' s) p_id"     
  then have "\<exists>!ch_id. port_in_channel conf (communication_' s) p_id ch_id \<and> 
            port_channel conf (communication_' s) p_id = ch_id"
    using port_unique_channel by auto 
 then have "chan_sampling (the (chans (communication_' s) (port_channel conf (communication_' s) p_id)))"    
    using a0 a1 a2  p_sampling_chan_sampling by fastforce 
 thus ?thesis using  sampling_insert_message
   unfolding port_get_messages_def port_in_channel_def
           Let_def  port_channel_def port_insert_message_def
            port_id_name_def port_exists_def
  by auto
qed

lemma port_insert:
 "state_conf  s \<Longrightarrow>
   port_open (communication_' s) p_id \<Longrightarrow>
   p_queuing conf (communication_' s) p_id \<and> 
   (port_get_messages conf (port_insert_message conf  (communication_' s)  p_id m t) p_id =
      port_get_messages conf  (communication_' s) p_id + {# m #}) \<or>
  p_sampling conf (communication_' s) p_id \<and> 
   (port_get_messages conf (port_insert_message conf  (communication_' s) p_id m t) p_id =
      {# m #}) "
proof-
  assume a0: "state_conf  s" and
         a1: " port_open (communication_' s) p_id"
  then have "p_sampling conf (communication_' s) p_id \<or> p_queuing conf (communication_' s) p_id"
    unfolding p_sampling_def p_queuing_def state_conf_def
  using queuing_or_sampling_port
  by (metis a0 ch_id_queuing_def ch_id_sampling_def port_channel_get_channel queuing_or_sampling_channel)       
  thus ?thesis 
   using queuing_port_insert[OF a0 a1, of m] sampling_port_insert[OF a0 a1]
  by fastforce
qed


  
lemma queuing_port_clear:
" state_conf  s \<Longrightarrow>
    port_open (communication_' s) p_id \<Longrightarrow>      
   port_get_messages conf 
         (port_clear_messages conf (communication_' s) p_id ) p_id = {#}
"
proof -
 assume a0: "state_conf  s" and
         a1: " port_open (communication_' s) p_id"                  
  then obtain ch_id where ch_id:"port_in_channel conf (communication_' s) p_id ch_id \<and> 
     port_channel conf (communication_' s) p_id = ch_id"
   using port_unique_channel by auto  
 thus ?thesis 
 using a0  ch_id
 unfolding port_get_messages_def 
           Let_def state_conf_def  port_clear_messages_def 
           channel_clear_messages_def channel_get_messages_def chan_queuing_def chan_sampling_def
           port_channel_def port_in_channel_def port_id_name_def port_name_in_channel_def port_exists_def
 apply clarify                           
  apply (cases "data (the (chans (communication_' s) ch_id))")   
   by auto 
qed

lemma channel_get_set_mutex:
"channel_get_mutex (channel_set_mutex ch i) = i"
unfolding channel_get_mutex_def channel_set_mutex_def
by auto

lemma port_get_set_mutex:
"port_get_mutex conf (port_set_mutex conf c p_id i) p_id = i"
  unfolding port_get_mutex_def port_set_mutex_def Let_def port_channel_def 
        port_in_channel_def port_id_name_def port_exists_def using channel_get_set_mutex
  by auto


lemma port_get_insert:"
       port_get_messages conf 
        (port_set_mutex conf 
          (port_insert_message conf c pt_id m t) pt_id v) pt_id = 
       port_get_messages conf (port_insert_message conf c pt_id m t) pt_id"
proof-
  show ?thesis 

  unfolding port_set_mutex_def Let_def port_insert_message_def channel_insert_message_def
    channel_set_mutex_def channel_set_messages_def channel_get_messages_def
 channel_set_messages_def 
          channel_insert_message_def chan_queuing_def channel_get_messages_def
           Let_def   port_insert_message_def  port_in_channel_def chan_sampling_def
           port_exists_def  port_id_name_def  port_open_def  port_exists_def
port_get_mutex_def channel_get_mutex_def port_get_messages_def
  by (auto simp add: port_channel_def port_in_channel_def port_id_name_def port_exists_def)
qed

lemma port_channl_eq_pid:"
ports (communication_' x) = ports (communication_' y) \<Longrightarrow> 
  port_channel conf (communication_' x) pid = 
  port_channel conf (communication_' y) pid"                                
 unfolding port_channel_def port_in_channel_def port_id_name_def port_exists_def by auto
     
lemma port_channl_eq_ports:"
ports (communication_' x) = ports (communication_' y) \<Longrightarrow> 
  port_channel conf (communication_' x) (pt (locals_' x ! i)) = 
  port_channel conf (communication_' y) (pt (locals_' x ! i))"                                
 using port_channl_eq_pid by auto


definition pre_comm
where
"pre_comm \<equiv> \<lbrace>\<forall>ch_id ch.  
              ((chans \<acute>communication) ch_id ) = Some ch \<longrightarrow>
              channel_get_mutex ch = 0\<rbrace>    
"

end

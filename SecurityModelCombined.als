open util/ordering[State]

sig Data {}
sig Device {}
sig Subsystem extends Device{}
sig Router extends Device{}
sig Channel {}
sig EngTerminal {}
sig Credential{}
sig Account{}


sig State {
  transmission_state_b: set Device lone -> lone Data,
  receive_state_b: set Device lone -> lone Data,

  generation_state_b: set Data lone -> lone Subsystem,
  generation_state_c: set Data -> lone Device,
  
  data_receive_state_b: set Data lone -> set Device,
  data_receive_state_c: set Data -> set Device,
  
  connected: set Channel -> set Device,
  carried_by: set Data -> lone Channel,

  compromised: set Device,
  can_authorise: set Subsystem,
  malicious: set Data,
  authorised: set Data,
  signed: set Data,	
  accepted: set Device -> set Data,

  secure:set Channel,

  //identity_of: set Device -> one Device,

  officially_recognised: set Subsystem,


  attempts_exceeded: set Account,
  limited: set Account,
  cracked: set Account,
  large: set Credential, 
  locked: set Account,
  has: set EngTerminal one -> some Account,
  hasCred: set Account one -> one Credential,

} {
  //accounts cannot be locked and cracked
  no locked & cracked
  //same goes for attempts_exceeded
  no attempts_exceeded & cracked
  //- each data object can only be one generation state
  no ~generation_state_b.generation_state_c

  //- subsystems can't transmit and receive data simultaneously
  no ~receive_state_b.transmission_state_b

  //- subsystem transitioning to transmission_b
  //- must be simultaneous with data moving to generation_b
  //~transmission_state_b = generation_state_b
  generation_state_b in ~transmission_state_b
  ~transmission_state_b in (generation_state_b + ~data_receive_state_c)
  ~receive_state_b = data_receive_state_b

  //- data in receive state must be in generate state c
  data_receive_state_b.Device in generation_state_c.Device
  data_receive_state_c.Device in generation_state_c.Device

  //- can't receive data twice
  no data_receive_state_c & data_receive_state_b

  //- subsystem can't receive it's own generated data
  no generation_state_c & data_receive_state_b
  no generation_state_c & data_receive_state_c

  //- generated data must be carried by a channel 
  generation_state_c.~connected in carried_by
  carried_by.Channel = (generation_state_c).Device

  //- all transmitting subsystems must connect to a channel
  transmission_state_b.Data in Channel.connected 

  //- all receiving subsystems must connect to the data-carrying channel
  receive_state_b.carried_by in ~connected

  //- uncompromised subsystems always have their own identity
  //Device.(identity_of & iden) = (Device - compromised) 	
}

fact {

  all s:State, s':s.next | s.has = s'.has

  all s:State, s':s.next | s.hasCred= s'.hasCred

  all s:State, s':s.next | s.cracked = s'.cracked

  all s:State, s':s.next, a:Account | 
  !(exceed_attempts[s',a]) => s.locked = s'.locked

  all s:State, s':s.next, a:Account | 
    a in s.locked => s.attempts_exceeded = s'.attempts_exceeded

  all s:State, s':s.next | s.large = s'.large

  all s:State, s':s.next | s.limited = s'.limited

  all s:State, s':s.next, c:Credential, a:Account| 
    (a->c) in s.hasCred && a in s.limited && c in s.large => !(a in s'.cracked)

  all s:State,s':s.next, a:Account |
    a in s.attempts_exceeded => a in s'.locked

 // all s:State | x:Subsystem | one r:Router | one c:Channel |
//		(c->x) in s.connected && (c->r) in s.connected
   //- CASE 1: no mitigation, all subsystems accept received data
   //all s:State | s.accepted = ~(s.data_receive_state_c)

   //- CASE 2a: compromised subsystems cannot accept data from secure channel
   all s:State | s.accepted in ~(s.data_receive_state_c)
 
   //all s:State, s':s.next, x:Device, d:Data |
   //         receive_end[s',x,d]
   //   && (x in s'.compromised)
   //   && (d.(s'.carried_by) in s'.secure)
   //   =>
   //   !((x->d) in s'.accepted)

   //- CASE 2b: subsystems will not accept unauthorised data
   all s:State, s':s.next, x:Device, d:Data |
            receive_end[s',x,d]
      && !(d in s'.authorised)
      =>
      !((x->d) in s'.accepted)   

   //- CASE 2c: uncompromised subsystems only receive data from
   //- officially recognised subsystems
  // all s:State, s':s.next, x:Device, d:Data |
  //          receive_end[s',x,d]
   //   && !(x in s'.compromised)
  //    && !(d.(s'.generation_state_c) in s'.officially_recognised)
  //    =>
  //    !((x->d) in s'.accepted)   
    //- the channel that carries data does not change
    //all s:State, s':s.next | s.carried_by in s'.carried_by 

    //- subsystems that accept data cannot later discard it
    all s:State, s':s.next, x:Device, d:Data |
      !receive_end[s',x,d] => (((x->d) in s.accepted) <=> ((x->d) in s'.accepted))

    //- data is signed or not, cannot change
    all s:State, s':s.next | s.signed = s'.signed
    //- data is either malicious or not (cannot change)
    all s:State, s':s.next, r:Router, d:Data | 
    !(receive_end[s',r,d]) => s.malicious = s'.malicious

    //- data is either authorised or not (cannot change)
    all s:State, s':s.next | s.authorised = s'.authorised 

    //- subsystems are either recognised or not (cannot change)
    all s:State, s':s.next | s.officially_recognised = s'.officially_recognised

  //- subsystems that receive malicious data become compromised
  all s:State, s':s.next, x:Device, d:Data |
    receive_end[s',x,d]  && d in s.malicious && (x->d) in s'.accepted => x in s'.compromised

  // compromised router turns data malicious if the data is not signed
  all s:State, s':s.next, r:Router, d:Data |
    receive_end[s',r,d]  && !(d in s.signed) && r in s.compromised && (r->d) in s'.accepted => d in s'.malicious

  all s:State, s':s.next, r:Router, d:Data |
    receive_end[s',r,d]  && d in s.signed && r in s.compromised && (r->d) in s'.accepted => !(d in s'.malicious)

  //- only compromised subsystems generate malicious data
  all s:State, s':s.next, x:Subsystem, d:Data |
    transmission_start[s',x,d]  && d in s.malicious => x in s'.compromised

  //- only can_authorise subsystems generate authorised data
  all s:State, s':s.next, x:Device, d:Data |
    transmission_start[s',x,d] && d in s.authorised => x in s'.can_authorise
  
  //- data in generate state c must have been in state b or c
  all s:State, s':s.next, d:Data |
        //- from b: stay in state b or go to state c
        d.(s.generation_state_b) in (d.(s'.generation_state_b) + d.(s'.generation_state_c))
        //- state c must come from b or c
   && d.(s'.generation_state_c) in (d.(s.generation_state_b) + d.(s.generation_state_c))
        //- from c: stay in state c
   && d.(s.generation_state_c) in d.(s'.generation_state_c)


  //- data in receive state c must have been in state b or c
  all s:State, s':s.next, x:Device |
        //- from b: stay in state b or go to state c
        (s.data_receive_state_b).x in ((s'.data_receive_state_b).x + (s'.data_receive_state_c).x)
        //- state c must come from b or c
   && (s'.data_receive_state_c).x in ((s.data_receive_state_b).x + (s.data_receive_state_c).x)
        //- from c: stay in state c
   && (s.data_receive_state_c).x in (s'.data_receive_state_c).x


   
  //- during transmission subsystems either continue transmission or finish
  //- (cannot immediately start transmitting new data)
  all s:State, s':s.next, x:Device |
    (no x.(s.transmission_state_b)) ||
    (x.(s'.transmission_state_b) in x.(s.transmission_state_b))

}

pred exceed_attempts[s':State, a:Account] {
  some s:s'.prev |
           !(a in s.attempts_exceeded) 
    && a in s'.attempts_exceeded
}

pred receive_end[s':State, x:Device, d:Data] {
  some s:s'.prev |
           (x->d) in s.receive_state_b 
    && !((x->d) in s'.receive_state_b)
}

pred transmission_start[s':State, x:Device, d:Data] {
  some s:s'.prev |
           (x->d) in s'.transmission_state_b 
    && !((x->d) in s.transmission_state_b)
}

//- scenario test: receiving malicious data
run {
  // mitigation signed data
  //all s:State | all d:Data | d in s.signed

  //test the condition
  some malicious
  some data_receive_state_c

  // filter out uninteresting things
  some accepted
  no x:Subsystem | x in State.compromised
  no first.accepted
  no first.generation_state_b
  no first.generation_state_c
  //some s:Subsystem | some d:Data | some s1:first.next | transmission_start[s1, s, d]
  //- subsystems are always connected to the (only) channel
  all s:State | all x:Subsystem | one c:Channel | (c->x) in s.connected
  all s:State | all r:Router| all c:Channel | (c->r) in s.connected
  all s:State, s':s.next |s.connected = s'.connected
  all s:State| all r:Router | r in s.compromised
  //- subsystem receives data, and was not compromised before that
  //some s:State, x:Subsystem, d:Data |
   // receive_end[s,x,d] && no (s.^prev).compromised

  //all s:State, s':s.next |s.carried_by = s'.carried_by

} for
exactly 5 State
, exactly 1 Subsystem
, exactly 1 Data
, exactly 2 Channel
, exactly 1 Router
, exactly 2 Device
, exactly 0 EngTerminal
, exactly 0 Account
, exactly 0 Credential

run {

 no first.locked
 no first.cracked
 some attempts_exceeded
 some cracked
 all s:State | all c:Credential | c in s.large 
 all s:State | all a:Account | a in s.limited

}for exactly 3 State,
exactly 1 EngTerminal,
exactly 1 Account,
exactly 1 Credential,
exactly 0 Subsystem,
exactly 0 Data,
exactly 0 Channel,
exactly 0 Router,
exactly 0 Device




//- subsystems can only send data that they received or generated
//- test: officially recognised subsystems

//- note: addition mitigation condition: discard data that
//- has your own identity (something suspicious clear is happening...)

//crack attempt exceeds a number -> model as relation, exceeded or not.

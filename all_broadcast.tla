------------------------------- MODULE all_broadcast -------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets
CONSTANT actorNo

(*--algorithm broadcast
  variables 
  null;
  queues = [id \in NODES |-> <<>>];
  stay_alive = TRUE;

  define
    NODES == 1 .. actorNo
    SENDER == {0}
  end define;
  
  macro receive(msg) begin
    await Len(queues[self]) # 0;
    msg := Head(queues[self]);
    queues[self] := Tail(queues[self]);
  end macro;
  
  macro forall(msg) begin
    queues := [id \in NODES |-> Append(queues[id], msg)];
  end macro;
  
  macro send(msg, to) begin
    queues[to] := queues[to] \o <<msg>>;
  end macro;

  fair process node \in NODES
  variables
    msg = <<>>,
    curr_stack = <<>>,
    
    delivered = {},
    messageCount = 0,

    rb_delivered = {},
    rb_vectorclock = "",
    rb_messageCount = 0,

    rco_temp_past_elem = 0,
    rco_temp_i = 0,

    rco_msg = 0,
    rco_delivered = {},
    rco_past = <<>>,
    rco_past_ids = {},
    rco_vectorclock = "",
    rco_messageCount = 0;
  begin
    node_loop:  while (stay_alive \/ Cardinality(delivered) = 0) do
    wait_for_msg:   receive(msg);
                    if (msg.type = "send") then
    send_network:       forall([
                            type |-> "receive",
                            stack |-> msg.stack,
                            body |-> msg.body
                        ]);
                    elsif (msg.type = "beb_broadcast") then
    beb_broadcast:      send([
                            type |-> "send",
                            stack |-> <<"receive">> \o msg.stack,
                            body |-> msg.body
                        ], self);
                    elsif (msg.type = "rb_broadcast") then
    rb_inc_clock:       rb_messageCount := rb_messageCount + 1;
                        rb_vectorclock := ToString(self) \o ToString(rb_messageCount);
    rb_broadcast:       send([
                            type |-> "beb_broadcast",
                            stack |-> <<"beb_deliver">> \o msg.stack,
                            body |-> [id |-> rb_vectorclock, content |-> msg.body]
                        ], self);
                    elsif (msg.type = "rco_broadcast") then
    rco_inc_clock:      rco_messageCount := rco_messageCount + 1;
                        rco_vectorclock := ToString(self) \o ToString(rco_messageCount);
                        rco_msg := [id |-> rco_vectorclock, past |-> rco_past, content |-> msg.body];
    rco_broadcast:      send([
                            type |-> "rb_broadcast",
                            stack |-> <<"rb_deliver">> \o msg.stack,
                            body |-> rco_msg
                        ], self);
                        rco_past := Append(rco_past, [sender |-> self, id |-> rco_vectorclock, content |-> msg.body]);
                        rco_past_ids := rco_past_ids \union {rco_vectorclock};
                    elsif (msg.type = "rb_deliver") then
    rco_stack:          curr_stack := <<>>;
    rco_curr_stack:     if (Len(msg.stack) > 0) then
                            curr_stack := Tail(msg.stack);
                        end if;
    rco_deliver:        if (Len(curr_stack) > 0) then
                            send([
                                type |-> Head(curr_stack),
                                stack |-> curr_stack,
                                body |-> msg.body
                            ], self);
                        end if;
                        if ~ ((msg.body).id \in rco_delivered) then
                            rco_temp_i := 1;
    iterate_over_past:      while(rco_temp_i <= Len((msg.body).past)) do
                                rco_temp_past_elem := (msg.body).past;
    iterate_read_past_elem:     rco_temp_past_elem := rco_temp_past_elem[rco_temp_i];
                                if ~ (rco_temp_past_elem.id \in rco_delivered) then
                                    rco_delivered := rco_delivered \union {rco_temp_past_elem.id};
                                    if ~ (rco_temp_past_elem.id \in rco_past_ids) then
                                        rco_past := Append(rco_past, rco_temp_past_elem);
                                        rco_past_ids := rco_past_ids \union {rco_temp_past_elem.id};
                                    end if;
                                end if;
                                rco_temp_i := rco_temp_i + 1;
                            end while;
                            rco_delivered := rco_delivered \union {(msg.body).id};
                        end if;
                    elsif (msg.type = "beb_deliver") then
    beb_stack:          curr_stack := <<>>;
    beb_curr_stack:     if (Len(msg.stack) > 0) then
                            curr_stack := Tail(msg.stack);
                        end if;
    beb_continue:       if (Len(curr_stack) > 0) then
                            send([
                                type |-> Head(curr_stack),
                                stack |-> curr_stack,
                                body |-> (msg.body).content
                            ], self);
                        end if;
    beb_deliver:        if ~ ((msg.body).id \in rb_delivered) then
                            rb_delivered := rb_delivered \union {(msg.body).id};
                            send([
                                type |-> "beb_broadcast",
                                stack |-> <<"beb_deliver">>,
                                body |-> msg.body
                            ], self);
                        end if;
                    elsif (msg.type = "receive") then
    receive_stack:      curr_stack := <<>>;
                        delivered := delivered \union {<<msg.body, messageCount>>};
    receive_curr_stack: if (Len(msg.stack) > 0) then
                            curr_stack := Tail(msg.stack);
                        end if;
                        messageCount := messageCount + 1;
    receive_network:    if (Len(curr_stack) > 0) then
                            send([
                                type |-> Head(curr_stack),
                                stack |-> curr_stack,
                                body |-> msg.body
                            ], self);
                        else
                            skip;
                        end if;
                    end if;
                end while;
    end process;
    
    fair process s \in SENDER
    variables
        msg_sent = null;
    begin
    send_something:     msg_sent := [
                            type |-> "beb_broadcast",
                            stack|-> <<>>,
                            body |-> "hello from germany"
                        ];
                        send(msg_sent, 1);
                        stay_alive := FALSE;
    end process;
end algorithm;
*)

\* BEGIN TRANSLATION (chksum(pcal) = "13fdb72b" /\ chksum(tla) = "35feb580")
CONSTANT defaultInitValue
VARIABLES null, queues, stay_alive, pc

(* define statement *)
NODES == 1 .. actorNo
SENDER == {0}

VARIABLES msg, curr_stack, delivered, messageCount, rb_delivered, 
          rb_vectorclock, rb_messageCount, rco_temp_past_elem, rco_temp_i, 
          rco_msg, rco_delivered, rco_past, rco_past_ids, rco_vectorclock, 
          rco_messageCount, msg_sent

vars == << null, queues, stay_alive, pc, msg, curr_stack, delivered, 
           messageCount, rb_delivered, rb_vectorclock, rb_messageCount, 
           rco_temp_past_elem, rco_temp_i, rco_msg, rco_delivered, rco_past, 
           rco_past_ids, rco_vectorclock, rco_messageCount, msg_sent >>

ProcSet == (NODES) \cup (SENDER)

Init == (* Global variables *)
        /\ null = defaultInitValue
        /\ queues = [id \in NODES |-> <<>>]
        /\ stay_alive = TRUE
        (* Process node *)
        /\ msg = [self \in NODES |-> <<>>]
        /\ curr_stack = [self \in NODES |-> <<>>]
        /\ delivered = [self \in NODES |-> {}]
        /\ messageCount = [self \in NODES |-> 0]
        /\ rb_delivered = [self \in NODES |-> {}]
        /\ rb_vectorclock = [self \in NODES |-> ""]
        /\ rb_messageCount = [self \in NODES |-> 0]
        /\ rco_temp_past_elem = [self \in NODES |-> 0]
        /\ rco_temp_i = [self \in NODES |-> 0]
        /\ rco_msg = [self \in NODES |-> 0]
        /\ rco_delivered = [self \in NODES |-> {}]
        /\ rco_past = [self \in NODES |-> <<>>]
        /\ rco_past_ids = [self \in NODES |-> {}]
        /\ rco_vectorclock = [self \in NODES |-> ""]
        /\ rco_messageCount = [self \in NODES |-> 0]
        (* Process s *)
        /\ msg_sent = [self \in SENDER |-> null]
        /\ pc = [self \in ProcSet |-> CASE self \in NODES -> "node_loop"
                                        [] self \in SENDER -> "send_something"]

node_loop(self) == /\ pc[self] = "node_loop"
                   /\ IF (stay_alive \/ Cardinality(delivered[self]) = 0)
                         THEN /\ pc' = [pc EXCEPT ![self] = "wait_for_msg"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << null, queues, stay_alive, msg, curr_stack, 
                                   delivered, messageCount, rb_delivered, 
                                   rb_vectorclock, rb_messageCount, 
                                   rco_temp_past_elem, rco_temp_i, rco_msg, 
                                   rco_delivered, rco_past, rco_past_ids, 
                                   rco_vectorclock, rco_messageCount, msg_sent >>

wait_for_msg(self) == /\ pc[self] = "wait_for_msg"
                      /\ Len(queues[self]) # 0
                      /\ msg' = [msg EXCEPT ![self] = Head(queues[self])]
                      /\ queues' = [queues EXCEPT ![self] = Tail(queues[self])]
                      /\ IF (msg'[self].type = "send")
                            THEN /\ pc' = [pc EXCEPT ![self] = "send_network"]
                            ELSE /\ IF (msg'[self].type = "beb_broadcast")
                                       THEN /\ pc' = [pc EXCEPT ![self] = "beb_broadcast"]
                                       ELSE /\ IF (msg'[self].type = "rb_broadcast")
                                                  THEN /\ pc' = [pc EXCEPT ![self] = "rb_inc_clock"]
                                                  ELSE /\ IF (msg'[self].type = "rco_broadcast")
                                                             THEN /\ pc' = [pc EXCEPT ![self] = "rco_inc_clock"]
                                                             ELSE /\ IF (msg'[self].type = "rb_deliver")
                                                                        THEN /\ pc' = [pc EXCEPT ![self] = "rco_stack"]
                                                                        ELSE /\ IF (msg'[self].type = "beb_deliver")
                                                                                   THEN /\ pc' = [pc EXCEPT ![self] = "beb_stack"]
                                                                                   ELSE /\ IF (msg'[self].type = "receive")
                                                                                              THEN /\ pc' = [pc EXCEPT ![self] = "receive_stack"]
                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "node_loop"]
                      /\ UNCHANGED << null, stay_alive, curr_stack, delivered, 
                                      messageCount, rb_delivered, 
                                      rb_vectorclock, rb_messageCount, 
                                      rco_temp_past_elem, rco_temp_i, rco_msg, 
                                      rco_delivered, rco_past, rco_past_ids, 
                                      rco_vectorclock, rco_messageCount, 
                                      msg_sent >>

send_network(self) == /\ pc[self] = "send_network"
                      /\ queues' = [id \in NODES |-> Append(queues[id], (       [
                                       type |-> "receive",
                                       stack |-> msg[self].stack,
                                       body |-> msg[self].body
                                   ]))]
                      /\ pc' = [pc EXCEPT ![self] = "node_loop"]
                      /\ UNCHANGED << null, stay_alive, msg, curr_stack, 
                                      delivered, messageCount, rb_delivered, 
                                      rb_vectorclock, rb_messageCount, 
                                      rco_temp_past_elem, rco_temp_i, rco_msg, 
                                      rco_delivered, rco_past, rco_past_ids, 
                                      rco_vectorclock, rco_messageCount, 
                                      msg_sent >>

beb_broadcast(self) == /\ pc[self] = "beb_broadcast"
                       /\ queues' = [queues EXCEPT ![self] = queues[self] \o <<(     [
                                                                 type |-> "send",
                                                                 stack |-> <<"receive">> \o msg[self].stack,
                                                                 body |-> msg[self].body
                                                             ])>>]
                       /\ pc' = [pc EXCEPT ![self] = "node_loop"]
                       /\ UNCHANGED << null, stay_alive, msg, curr_stack, 
                                       delivered, messageCount, rb_delivered, 
                                       rb_vectorclock, rb_messageCount, 
                                       rco_temp_past_elem, rco_temp_i, rco_msg, 
                                       rco_delivered, rco_past, rco_past_ids, 
                                       rco_vectorclock, rco_messageCount, 
                                       msg_sent >>

rb_inc_clock(self) == /\ pc[self] = "rb_inc_clock"
                      /\ rb_messageCount' = [rb_messageCount EXCEPT ![self] = rb_messageCount[self] + 1]
                      /\ rb_vectorclock' = [rb_vectorclock EXCEPT ![self] = ToString(self) \o ToString(rb_messageCount'[self])]
                      /\ pc' = [pc EXCEPT ![self] = "rb_broadcast"]
                      /\ UNCHANGED << null, queues, stay_alive, msg, 
                                      curr_stack, delivered, messageCount, 
                                      rb_delivered, rco_temp_past_elem, 
                                      rco_temp_i, rco_msg, rco_delivered, 
                                      rco_past, rco_past_ids, rco_vectorclock, 
                                      rco_messageCount, msg_sent >>

rb_broadcast(self) == /\ pc[self] = "rb_broadcast"
                      /\ queues' = [queues EXCEPT ![self] = queues[self] \o <<(     [
                                                                type |-> "beb_broadcast",
                                                                stack |-> <<"beb_deliver">> \o msg[self].stack,
                                                                body |-> [id |-> rb_vectorclock[self], content |-> msg[self].body]
                                                            ])>>]
                      /\ pc' = [pc EXCEPT ![self] = "node_loop"]
                      /\ UNCHANGED << null, stay_alive, msg, curr_stack, 
                                      delivered, messageCount, rb_delivered, 
                                      rb_vectorclock, rb_messageCount, 
                                      rco_temp_past_elem, rco_temp_i, rco_msg, 
                                      rco_delivered, rco_past, rco_past_ids, 
                                      rco_vectorclock, rco_messageCount, 
                                      msg_sent >>

rco_inc_clock(self) == /\ pc[self] = "rco_inc_clock"
                       /\ rco_messageCount' = [rco_messageCount EXCEPT ![self] = rco_messageCount[self] + 1]
                       /\ rco_vectorclock' = [rco_vectorclock EXCEPT ![self] = ToString(self) \o ToString(rco_messageCount'[self])]
                       /\ rco_msg' = [rco_msg EXCEPT ![self] = [id |-> rco_vectorclock'[self], past |-> rco_past[self], content |-> msg[self].body]]
                       /\ pc' = [pc EXCEPT ![self] = "rco_broadcast"]
                       /\ UNCHANGED << null, queues, stay_alive, msg, 
                                       curr_stack, delivered, messageCount, 
                                       rb_delivered, rb_vectorclock, 
                                       rb_messageCount, rco_temp_past_elem, 
                                       rco_temp_i, rco_delivered, rco_past, 
                                       rco_past_ids, msg_sent >>

rco_broadcast(self) == /\ pc[self] = "rco_broadcast"
                       /\ queues' = [queues EXCEPT ![self] = queues[self] \o <<(     [
                                                                 type |-> "rb_broadcast",
                                                                 stack |-> <<"rb_deliver">> \o msg[self].stack,
                                                                 body |-> rco_msg[self]
                                                             ])>>]
                       /\ rco_past' = [rco_past EXCEPT ![self] = Append(rco_past[self], [sender |-> self, id |-> rco_vectorclock[self], content |-> msg[self].body])]
                       /\ rco_past_ids' = [rco_past_ids EXCEPT ![self] = rco_past_ids[self] \union {rco_vectorclock[self]}]
                       /\ pc' = [pc EXCEPT ![self] = "node_loop"]
                       /\ UNCHANGED << null, stay_alive, msg, curr_stack, 
                                       delivered, messageCount, rb_delivered, 
                                       rb_vectorclock, rb_messageCount, 
                                       rco_temp_past_elem, rco_temp_i, rco_msg, 
                                       rco_delivered, rco_vectorclock, 
                                       rco_messageCount, msg_sent >>

rco_stack(self) == /\ pc[self] = "rco_stack"
                   /\ curr_stack' = [curr_stack EXCEPT ![self] = <<>>]
                   /\ pc' = [pc EXCEPT ![self] = "rco_curr_stack"]
                   /\ UNCHANGED << null, queues, stay_alive, msg, delivered, 
                                   messageCount, rb_delivered, rb_vectorclock, 
                                   rb_messageCount, rco_temp_past_elem, 
                                   rco_temp_i, rco_msg, rco_delivered, 
                                   rco_past, rco_past_ids, rco_vectorclock, 
                                   rco_messageCount, msg_sent >>

rco_curr_stack(self) == /\ pc[self] = "rco_curr_stack"
                        /\ IF (Len(msg[self].stack) > 0)
                              THEN /\ curr_stack' = [curr_stack EXCEPT ![self] = Tail(msg[self].stack)]
                              ELSE /\ TRUE
                                   /\ UNCHANGED curr_stack
                        /\ pc' = [pc EXCEPT ![self] = "rco_deliver"]
                        /\ UNCHANGED << null, queues, stay_alive, msg, 
                                        delivered, messageCount, rb_delivered, 
                                        rb_vectorclock, rb_messageCount, 
                                        rco_temp_past_elem, rco_temp_i, 
                                        rco_msg, rco_delivered, rco_past, 
                                        rco_past_ids, rco_vectorclock, 
                                        rco_messageCount, msg_sent >>

rco_deliver(self) == /\ pc[self] = "rco_deliver"
                     /\ IF (Len(curr_stack[self]) > 0)
                           THEN /\ queues' = [queues EXCEPT ![self] = queues[self] \o <<(     [
                                                                          type |-> Head(curr_stack[self]),
                                                                          stack |-> curr_stack[self],
                                                                          body |-> msg[self].body
                                                                      ])>>]
                           ELSE /\ TRUE
                                /\ UNCHANGED queues
                     /\ IF ~ ((msg[self].body).id \in rco_delivered[self])
                           THEN /\ rco_temp_i' = [rco_temp_i EXCEPT ![self] = 1]
                                /\ pc' = [pc EXCEPT ![self] = "iterate_over_past"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "node_loop"]
                                /\ UNCHANGED rco_temp_i
                     /\ UNCHANGED << null, stay_alive, msg, curr_stack, 
                                     delivered, messageCount, rb_delivered, 
                                     rb_vectorclock, rb_messageCount, 
                                     rco_temp_past_elem, rco_msg, 
                                     rco_delivered, rco_past, rco_past_ids, 
                                     rco_vectorclock, rco_messageCount, 
                                     msg_sent >>

iterate_over_past(self) == /\ pc[self] = "iterate_over_past"
                           /\ IF (rco_temp_i[self] <= Len((msg[self].body).past))
                                 THEN /\ rco_temp_past_elem' = [rco_temp_past_elem EXCEPT ![self] = (msg[self].body).past]
                                      /\ pc' = [pc EXCEPT ![self] = "iterate_read_past_elem"]
                                      /\ UNCHANGED rco_delivered
                                 ELSE /\ rco_delivered' = [rco_delivered EXCEPT ![self] = rco_delivered[self] \union {(msg[self].body).id}]
                                      /\ pc' = [pc EXCEPT ![self] = "node_loop"]
                                      /\ UNCHANGED rco_temp_past_elem
                           /\ UNCHANGED << null, queues, stay_alive, msg, 
                                           curr_stack, delivered, messageCount, 
                                           rb_delivered, rb_vectorclock, 
                                           rb_messageCount, rco_temp_i, 
                                           rco_msg, rco_past, rco_past_ids, 
                                           rco_vectorclock, rco_messageCount, 
                                           msg_sent >>

iterate_read_past_elem(self) == /\ pc[self] = "iterate_read_past_elem"
                                /\ rco_temp_past_elem' = [rco_temp_past_elem EXCEPT ![self] = rco_temp_past_elem[self][rco_temp_i[self]]]
                                /\ IF ~ (rco_temp_past_elem'[self].id \in rco_delivered[self])
                                      THEN /\ rco_delivered' = [rco_delivered EXCEPT ![self] = rco_delivered[self] \union {rco_temp_past_elem'[self].id}]
                                           /\ IF ~ (rco_temp_past_elem'[self].id \in rco_past_ids[self])
                                                 THEN /\ rco_past' = [rco_past EXCEPT ![self] = Append(rco_past[self], rco_temp_past_elem'[self])]
                                                      /\ rco_past_ids' = [rco_past_ids EXCEPT ![self] = rco_past_ids[self] \union {rco_temp_past_elem'[self].id}]
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED << rco_past, 
                                                                      rco_past_ids >>
                                      ELSE /\ TRUE
                                           /\ UNCHANGED << rco_delivered, 
                                                           rco_past, 
                                                           rco_past_ids >>
                                /\ rco_temp_i' = [rco_temp_i EXCEPT ![self] = rco_temp_i[self] + 1]
                                /\ pc' = [pc EXCEPT ![self] = "iterate_over_past"]
                                /\ UNCHANGED << null, queues, stay_alive, msg, 
                                                curr_stack, delivered, 
                                                messageCount, rb_delivered, 
                                                rb_vectorclock, 
                                                rb_messageCount, rco_msg, 
                                                rco_vectorclock, 
                                                rco_messageCount, msg_sent >>

beb_stack(self) == /\ pc[self] = "beb_stack"
                   /\ curr_stack' = [curr_stack EXCEPT ![self] = <<>>]
                   /\ pc' = [pc EXCEPT ![self] = "beb_curr_stack"]
                   /\ UNCHANGED << null, queues, stay_alive, msg, delivered, 
                                   messageCount, rb_delivered, rb_vectorclock, 
                                   rb_messageCount, rco_temp_past_elem, 
                                   rco_temp_i, rco_msg, rco_delivered, 
                                   rco_past, rco_past_ids, rco_vectorclock, 
                                   rco_messageCount, msg_sent >>

beb_curr_stack(self) == /\ pc[self] = "beb_curr_stack"
                        /\ IF (Len(msg[self].stack) > 0)
                              THEN /\ curr_stack' = [curr_stack EXCEPT ![self] = Tail(msg[self].stack)]
                              ELSE /\ TRUE
                                   /\ UNCHANGED curr_stack
                        /\ pc' = [pc EXCEPT ![self] = "beb_continue"]
                        /\ UNCHANGED << null, queues, stay_alive, msg, 
                                        delivered, messageCount, rb_delivered, 
                                        rb_vectorclock, rb_messageCount, 
                                        rco_temp_past_elem, rco_temp_i, 
                                        rco_msg, rco_delivered, rco_past, 
                                        rco_past_ids, rco_vectorclock, 
                                        rco_messageCount, msg_sent >>

beb_continue(self) == /\ pc[self] = "beb_continue"
                      /\ IF (Len(curr_stack[self]) > 0)
                            THEN /\ queues' = [queues EXCEPT ![self] = queues[self] \o <<(     [
                                                                           type |-> Head(curr_stack[self]),
                                                                           stack |-> curr_stack[self],
                                                                           body |-> (msg[self].body).content
                                                                       ])>>]
                            ELSE /\ TRUE
                                 /\ UNCHANGED queues
                      /\ pc' = [pc EXCEPT ![self] = "beb_deliver"]
                      /\ UNCHANGED << null, stay_alive, msg, curr_stack, 
                                      delivered, messageCount, rb_delivered, 
                                      rb_vectorclock, rb_messageCount, 
                                      rco_temp_past_elem, rco_temp_i, rco_msg, 
                                      rco_delivered, rco_past, rco_past_ids, 
                                      rco_vectorclock, rco_messageCount, 
                                      msg_sent >>

beb_deliver(self) == /\ pc[self] = "beb_deliver"
                     /\ IF ~ ((msg[self].body).id \in rb_delivered[self])
                           THEN /\ rb_delivered' = [rb_delivered EXCEPT ![self] = rb_delivered[self] \union {(msg[self].body).id}]
                                /\ queues' = [queues EXCEPT ![self] = queues[self] \o <<(     [
                                                                          type |-> "beb_broadcast",
                                                                          stack |-> <<"beb_deliver">>,
                                                                          body |-> msg[self].body
                                                                      ])>>]
                           ELSE /\ TRUE
                                /\ UNCHANGED << queues, rb_delivered >>
                     /\ pc' = [pc EXCEPT ![self] = "node_loop"]
                     /\ UNCHANGED << null, stay_alive, msg, curr_stack, 
                                     delivered, messageCount, rb_vectorclock, 
                                     rb_messageCount, rco_temp_past_elem, 
                                     rco_temp_i, rco_msg, rco_delivered, 
                                     rco_past, rco_past_ids, rco_vectorclock, 
                                     rco_messageCount, msg_sent >>

receive_stack(self) == /\ pc[self] = "receive_stack"
                       /\ curr_stack' = [curr_stack EXCEPT ![self] = <<>>]
                       /\ delivered' = [delivered EXCEPT ![self] = delivered[self] \union {<<msg[self].body, messageCount[self]>>}]
                       /\ pc' = [pc EXCEPT ![self] = "receive_curr_stack"]
                       /\ UNCHANGED << null, queues, stay_alive, msg, 
                                       messageCount, rb_delivered, 
                                       rb_vectorclock, rb_messageCount, 
                                       rco_temp_past_elem, rco_temp_i, rco_msg, 
                                       rco_delivered, rco_past, rco_past_ids, 
                                       rco_vectorclock, rco_messageCount, 
                                       msg_sent >>

receive_curr_stack(self) == /\ pc[self] = "receive_curr_stack"
                            /\ IF (Len(msg[self].stack) > 0)
                                  THEN /\ curr_stack' = [curr_stack EXCEPT ![self] = Tail(msg[self].stack)]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED curr_stack
                            /\ messageCount' = [messageCount EXCEPT ![self] = messageCount[self] + 1]
                            /\ pc' = [pc EXCEPT ![self] = "receive_network"]
                            /\ UNCHANGED << null, queues, stay_alive, msg, 
                                            delivered, rb_delivered, 
                                            rb_vectorclock, rb_messageCount, 
                                            rco_temp_past_elem, rco_temp_i, 
                                            rco_msg, rco_delivered, rco_past, 
                                            rco_past_ids, rco_vectorclock, 
                                            rco_messageCount, msg_sent >>

receive_network(self) == /\ pc[self] = "receive_network"
                         /\ IF (Len(curr_stack[self]) > 0)
                               THEN /\ queues' = [queues EXCEPT ![self] = queues[self] \o <<(     [
                                                                              type |-> Head(curr_stack[self]),
                                                                              stack |-> curr_stack[self],
                                                                              body |-> msg[self].body
                                                                          ])>>]
                               ELSE /\ TRUE
                                    /\ UNCHANGED queues
                         /\ pc' = [pc EXCEPT ![self] = "node_loop"]
                         /\ UNCHANGED << null, stay_alive, msg, curr_stack, 
                                         delivered, messageCount, rb_delivered, 
                                         rb_vectorclock, rb_messageCount, 
                                         rco_temp_past_elem, rco_temp_i, 
                                         rco_msg, rco_delivered, rco_past, 
                                         rco_past_ids, rco_vectorclock, 
                                         rco_messageCount, msg_sent >>

node(self) == node_loop(self) \/ wait_for_msg(self) \/ send_network(self)
                 \/ beb_broadcast(self) \/ rb_inc_clock(self)
                 \/ rb_broadcast(self) \/ rco_inc_clock(self)
                 \/ rco_broadcast(self) \/ rco_stack(self)
                 \/ rco_curr_stack(self) \/ rco_deliver(self)
                 \/ iterate_over_past(self) \/ iterate_read_past_elem(self)
                 \/ beb_stack(self) \/ beb_curr_stack(self)
                 \/ beb_continue(self) \/ beb_deliver(self)
                 \/ receive_stack(self) \/ receive_curr_stack(self)
                 \/ receive_network(self)

send_something(self) == /\ pc[self] = "send_something"
                        /\ msg_sent' = [msg_sent EXCEPT ![self] =             [
                                                                      type |-> "beb_broadcast",
                                                                      stack|-> <<>>,
                                                                      body |-> "hello from germany"
                                                                  ]]
                        /\ queues' = [queues EXCEPT ![1] = queues[1] \o <<msg_sent'[self]>>]
                        /\ stay_alive' = FALSE
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << null, msg, curr_stack, delivered, 
                                        messageCount, rb_delivered, 
                                        rb_vectorclock, rb_messageCount, 
                                        rco_temp_past_elem, rco_temp_i, 
                                        rco_msg, rco_delivered, rco_past, 
                                        rco_past_ids, rco_vectorclock, 
                                        rco_messageCount >>

s(self) == send_something(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in NODES: node(self))
           \/ (\E self \in SENDER: s(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in NODES : WF_vars(node(self))
        /\ \A self \in SENDER : WF_vars(s(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Invariants

EventualDelivery == <>(\A n \in NODES: Cardinality(delivered[n]) # 0)

====

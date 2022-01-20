MACHINE CXCC_CXCC
SETS Nodes = {n1,n2,n3}; Packets0 = {nopack, p1, p2, p3}; Flow = {f1}
CONSTANTS
  origin,dest, route, Packets
PROPERTIES
  Packets = Packets0 - {nopack} &
  origin: Flow --> Nodes &
  dest: Flow --> Nodes &
  !f.(f:Flow => origin(f) /= dest(f)) &
  route: Flow --> perm(Nodes) & 
  size(route(f1))>2 &
  !f.(f:Flow => (first(route(f)) = origin(f) &
                last(route(f))= dest(f)) )
ASSERTIONS
  !f.(f:Flow => (first(route(f)) = origin(f) &
                last(route(f))= dest(f)) );
  first(route(f1)) = origin(f1);
  last(route(f1)) = dest(f1)
 VARIABLES
   in_queue, out_queue, used_packets
 INVARIANT
   in_queue: (Flow*Nodes --> Packets0) &
   out_queue: (Flow*Nodes --> Packets0)  &
   used_packets: Flow --> POW(Packets0) &
   !(f,i).(f:Flow & i:NATURAL1 & i:1..size(route(f))-1 &
     (in_queue(f|->route(f)(i+1)) /= nopack)
     => ( (out_queue(f|->route(f)(i)) /= nopack) &
           in_queue(f|->route(f)(i+1)) = out_queue(f|->route(f)(i)))
        )
 INITIALISATION
   in_queue :: (Flow*Nodes) --> {nopack} ||
   out_queue :: (Flow*Nodes) --> {nopack} ||
   used_packets := %f.(f:Flow|{})
 OPERATIONS

   generate_packet(f,packet) = 
   PRE f:Flow &
       in_queue(f|->origin(f)) = nopack &
       packet:Packets &
       packet /: used_packets(f)
   THEN
       in_queue(f|->origin(f)) := packet ||
       used_packets(f) := used_packets(f) \/ {packet}
   END;

   shift_packet(f,n) =
   PRE f:Flow &
       n:Nodes &
       out_queue(f|->n) = nopack & 
       in_queue(f|->n) /= nopack &
       n /= dest(f)
   THEN
      out_queue(f|->n) := in_queue(f|->n);
      in_queue(f|->n) := nopack
   END;

   consume_packet(f,n,p,pre) =
   PRE f:Flow & 
       n:Nodes & 
       n = dest(f) &
       in_queue(f|->n) /= nopack &
       p:Packets &
       in_queue(f|->n) = p &
       pre:Nodes &
       #i.(i:NATURAL1 & i:2..size(route(f)) & route(f)(i)=n & route(f)(i-1)=pre)
   THEN
      CHOICE
         out_queue(f|->pre) := nopack
      OR
         skip 
      END 
      ||
      in_queue(f|->n) := nopack
   END;

   send_packet_succ(f,n,p,suc) =
   PRE f:Flow &
       n:Nodes &
       p:Packets &
       n /= dest(f) &
       out_queue(f|->n) /= nopack &
       out_queue(f|->n) = p &
       suc:Nodes &
       #i.(i:1..size(route(f))-1 & route(f)(i)=n & route(f)(i+1)=suc)
   THEN
       in_queue(f|->suc) := p 
   END;

   send_imp_ack_succ(f,n,p,pre) =
   PRE f:Flow &
       n:Nodes &
       p:Packets &
       n /= dest(f) &
       n /= origin(f) &
       out_queue(f|->n) /= nopack &
       out_queue(f|->n) = p &
       pre:Nodes &
       #i.(i:2..size(route(f)) & route(f)(i)=n & route(f)(i-1)=pre)
   THEN
       out_queue(f|->pre) := nopack ;
       in_queue(f|->n) := nopack
   END;

   finalise_mc = 
   PRE
     !(fl).(fl : Flow => used_packets(fl) = Packets) &
     !(fl,nd).((fl : Flow & nd: Nodes) => (in_queue(fl |-> nd) = nopack & out_queue(fl |-> nd) = nopack))
   THEN
     skip
   END

END

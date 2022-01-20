MODEL
   ImpAckProtocol
   /* First model of a protocol for wireless networks with implicit
      acknowledgement (a device can observe whether its message has
      been forwarded) and flow control (only send further packets
      if the previous packet has been acknowledged by the successor;
      it doesn't necessarily have to have been arrived at the destination) */
  /* Not yet modelled: messages being lost and explicit request for ack
     messages */
  /* Notes with MSG_SIZE = 5 and 3 devices:
     942 nodes; with symmetry markers 271  */
SETS
  Devices = {D1, D2, D3}
 CONSTANTS
  connected
 PROPERTIES
    connected: Devices <-> Devices  & /* which devices can speak to each other */
    connected = connected~ & /* symmetric relation */
    id(Devices) /\ connected = {} /* anti-reflexive */
    
    & dom(connected) = Devices  /* does not yet ensure complete connectness */
DEFINITIONS
  MSG_SIZE == 3 ;
  origin == first(route);
  destination == last(route);
  dest_pred == last(front(route));
  ROUTE_INV == (route: perm(Devices) &   /* we have just one route */
           size(route)>1 &
           !ri.(ri:1..(size(route)-1) => route(ri)|->route(ri+1) : connected))
VARIABLES
    route, sent, imp_ack, Messages, AckMessages, Buffer
INVARIANT 
   ROUTE_INV &
   sent: Devices --> 0..MSG_SIZE &
   imp_ack: Devices --> 0..MSG_SIZE &
   Buffer: Devices --> -1..MSG_SIZE &
   Messages : Devices --> POW(Devices * (0..MSG_SIZE)) & 
   AckMessages : Devices --> POW(Devices * (0..MSG_SIZE)) &
   !si.(si:1..(size(route)-1) => sent(route(si)) <= sent(route(si+1))+1) &
   !dd.(dd:Devices => sent(dd) >= imp_ack(dd)) &
   !dv.(dv:Devices => (card(Messages(dv)) <= MSG_SIZE & card(AckMessages(dv)) <= MSG_SIZE))
INITIALISATION
  route : (ROUTE_INV) ||
  sent := %x.(x:Devices|0) || imp_ack := %x.(x:Devices|0) ||
  Buffer :: Devices --> {-1} ||
  Messages := %x.(x:Devices|{}) || AckMessages := %x.(x:Devices|{})
OPERATIONS

  add_packet(nr) = 
  PRE nr = sent(origin)+1 & Buffer(origin) = -1 &
      nr <= MSG_SIZE
  THEN
     Buffer(origin) := nr
  END;

  send_packet(nr,from,to,i) =
  PRE from : Devices & 
      to : Devices &
      from/= to &
      Buffer(from) /= -1 &
      nr = Buffer(from) &
      i : 1..(size(route)-1) &
      from = route(i) &
      to = route(i+1) &
      imp_ack(from) = nr-1
  THEN
      sent(from) := nr ||
      Buffer(from) := -1 ||
      Messages(from) := Messages(from) \/ { to |-> nr }
  END;

  receive_packet(nr,from,to) = 
  PRE to:Devices &
      nr: 0..MSG_SIZE & 
      nr > sent(to) &
      from: Devices &
      from |-> to : connected &
      to |-> nr : Messages(from) &
      Buffer(to) = -1
  THEN
      Buffer(to) := nr
  END;

  receive_imp_ack(nr,from,i) =
  PRE nr : 0..MSG_SIZE &
      from : Devices &
      i : 1..size(route)-2 &
      from = route(i) &
      route(i+2) |-> nr : Messages(route(i+1)) &
      imp_ack(from) < nr
  THEN
      imp_ack(from) := nr
  END;

  receive_explicit_ack(node,from,nr) =
  PRE node:Devices &
      nr:0..MSG_SIZE &
      from: Devices &
      from |-> node: connected &
      node |-> nr : AckMessages(from) &
      nr> imp_ack(from)
  THEN
      imp_ack(from) := nr
  END;

  arrive_packet(nr) =
  PRE nr : 0..MSG_SIZE &
      Buffer(destination) /= -1 &
      (Buffer(destination) /= -1 => Buffer(destination) = nr)
  THEN
      Buffer(destination) := -1 ||
      AckMessages(dest_pred) := AckMessages(dest_pred) \/ { destination |-> nr } ||
      sent(destination) := nr
  END;

  finished =
  PRE sent(destination) = MSG_SIZE
  THEN skip
  END
END

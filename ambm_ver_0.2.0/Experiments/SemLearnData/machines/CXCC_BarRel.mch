MACHINE CXCC_BarRel
/* Model developed on 15/2/2008 in about 1h30 */
SETS
 NODES = {k0,k1,k2}; Packets = {NoPacket,P1,P2,P3,ACK}

CONSTANTS route, expack
PROPERTIES
 route: perm(NODES) & expack:Packets &
 card(Packets)>1 &
 expack = ACK & route = [k0,k1,k2]
VARIABLES pout,pin,pinlast,ether,to_send
INVARIANT
 /* pin, pout, pinlast model local variables of each node */
 pout: NODES --> Packets &
 pin: NODES --> Packets &
 pinlast: NODES --> Packets &
 
 /* This models the transmission ether */
 ether: NODES --> Packets &
 card(ether) <= card(NODES) &
 
 /* This models the packets that should be sent */
 to_send : POW(Packets - {expack, NoPacket})
INITIALISATION 
  pout :: NODES --> {NoPacket} ||
  pin :: NODES --> {NoPacket} ||
  pinlast :: NODES --> {NoPacket} ||
  ether :: NODES --> {NoPacket} || 
  to_send := {P1,P2,P3}
OPERATIONS
  GenerateNewPacket(p) =
        PRE p:(Packets - {expack, NoPacket}) &
            pin(route(1)) = NoPacket &
            to_send /= {} &
            p : to_send
        THEN
            pin(route(1)) := p ||
            to_send := to_send - {p}
        END;

  SendPacketFirstTime(n,p,i) =
        PRE ran(ether) = {NoPacket} & 
            p:(Packets - {expack, NoPacket}) & 
            n:NODES &
            not(pin(n) = NoPacket) &
            i:1..(size(route)-1) &
            route(i) = n & 
            pin(n) = p & 
            pout(n) = NoPacket
        THEN
            pout(n) := p ||
            pin(n) := NoPacket ||
            ether(route(i+1)) := p
        END;

  
  RetransmitPacket(n,p,i) =
        PRE ran(ether) = {NoPacket} &
            p:(Packets - {expack, NoPacket}) &
            n:NODES &
            i:1..(size(route)-1) &
            route(i) = n &
            not(pout(n) = NoPacket) &
            pout(n) = p
        THEN
            ether(route(i+1)) := p
        END;
  
  ReceivePacket(n,p,i) =
        PRE n:NODES &
            p:(Packets - {expack, NoPacket}) &
            not(ether(n) = NoPacket) &
            ether(n) = p & 
            i:1..size(route) &
            route(i) = n
        THEN
            IF not(pinlast(n) = NoPacket) & p = pinlast(n) THEN
              IF not(pin(n) = NoPacket) THEN
                 SELECT pin(n) = p THEN skip END;
                 ether(n) := NoPacket
              ELSE
                 ether(route(i-1)) := expack;
                 ether(n) := NoPacket
              END
            ELSE
               SELECT pin(n) = NoPacket THEN
                  pin(n) := p ||
                  pinlast(n) := p ||
                  ether(n) := NoPacket
               END
            END
        END;

  ReceiveImpAck(n,i,p) =
        PRE n:NODES &
            i:1..size(route)-2 &
            route(i) = n &
            p:(Packets - {expack, NoPacket}) &
            ether(route(i+2)) = p &
            not(pout(n) = NoPacket) &
            pout(n) = p
        THEN
            pout(n) := NoPacket
        END;

  ReceiveExpAck(n) =
        PRE n:NODES &
            not(ether(n) = NoPacket) &
            ether(n) = expack
        THEN
            SELECT not(pout(n) = NoPacket) THEN
              pout(n) := NoPacket ||
              ether(n) := NoPacket
            END
        END;

  DropPacket(n,p) =
        PRE n:NODES &
            p:Packets - {NoPacket} &
            not(ether(n) = NoPacket) &
            ether(n) = p
        THEN
            ether(n) := NoPacket
        END;

  ReceiveEndPacket(p) =
        PRE p:(Packets - {expack, NoPacket}) &
            not(pin(route(size(route))) = NoPacket) &
            pin(route(size(route))) = p & 
            ether(route(size(route)-1)) = NoPacket &
            ran(ether) = {NoPacket}
        THEN
            pin(route(size(route))) := NoPacket ||
            ether(route(size(route)-1)) := expack
        END;

  Finished =
        PRE ran(pout) = {NoPacket} &
            ran(pin) = {NoPacket} &
            ran(ether) = {NoPacket} &
            to_send = {}
        THEN
            skip
        END
  
END

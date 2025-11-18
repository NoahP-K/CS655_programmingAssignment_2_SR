import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.*;

public class StudentNetworkSimulator extends NetworkSimulator
{
    /*
     * Predefined Constants (static member variables):
     *
     *   int MAXDATASIZE : the maximum size of the Message data and
     *                     Packet payload
     *
     *   int A           : a predefined integer that represents entity A
     *   int B           : a predefined integer that represents entity B 
     *
     * Predefined Member Methods:
     *
     *  void stopTimer(int entity): 
     *       Stops the timer running at "entity" [A or B]
     *  void startTimer(int entity, double increment): 
     *       Starts a timer running at "entity" [A or B], which will expire in
     *       "increment" time units, causing the interrupt handler to be
     *       called.  You should only call this with A.
     *  void toLayer3(int callingEntity, Packet p)
     *       Puts the packet "p" into the network from "callingEntity" [A or B]
     *  void toLayer5(String dataSent)
     *       Passes "dataSent" up to layer 5
     *  double getTime()
     *       Returns the current time in the simulator.  Might be useful for
     *       debugging.
     *  int getTraceLevel()
     *       Returns TraceLevel
     *  void printEventList()
     *       Prints the current event list to stdout.  Might be useful for
     *       debugging, but probably not.
     *
     *
     *  Predefined Classes:
     *
     *  Message: Used to encapsulate a message coming from layer 5
     *    Constructor:
     *      Message(String inputData): 
     *          creates a new Message containing "inputData"
     *    Methods:
     *      boolean setData(String inputData):
     *          sets an existing Message's data to "inputData"
     *          returns true on success, false otherwise
     *      String getData():
     *          returns the data contained in the message
     *  Packet: Used to encapsulate a packet
     *    Constructors:
     *      Packet (Packet p):
     *          creates a new Packet that is a copy of "p"
     *      Packet (int seq, int ack, int check, String newPayload)
     *          creates a new Packet with a sequence field of "seq", an
     *          ack field of "ack", a checksum field of "check", and a
     *          payload of "newPayload"
     *      Packet (int seq, int ack, int check)
     *          chreate a new Packet with a sequence field of "seq", an
     *          ack field of "ack", a checksum field of "check", and
     *          an empty payload
     *    Methods:
     *      boolean setSeqnum(int n)
     *          sets the Packet's sequence field to "n"
     *          returns true on success, false otherwise
     *      boolean setAcknum(int n)
     *          sets the Packet's ack field to "n"
     *          returns true on success, false otherwise
     *      boolean setChecksum(int n)
     *          sets the Packet's checksum to "n"
     *          returns true on success, false otherwise
     *      boolean setPayload(String newPayload)
     *          sets the Packet's payload to "newPayload"
     *          returns true on success, false otherwise
     *      int getSeqnum()
     *          returns the contents of the Packet's sequence field
     *      int getAcknum()
     *          returns the contents of the Packet's ack field
     *      int getChecksum()
     *          returns the checksum of the Packet
     *      int getPayload()
     *          returns the Packet's payload
     *
     */

    /*   Please use the following variables in your routines.
     *   int WindowSize  : the window size
     *   double RxmtInterval   : the retransmission timeout
     *   int LimitSeqNo  : when sequence number reaches this value, it wraps around
     */

    public static final int FirstSeqNo = 0;
    private int WindowSize;
    private double RxmtInterval;
    private int LimitSeqNo;
    
    // Add any necessary class variables here.  Remember, you cannot use
    // these variables to send messages error free!  They can only hold
    // state information for A or B.
    // Also add any necessary methods (e.g. checksum of a String)

    //side A class variables:
    int numTransmittedPackets_A;    //number of unique packets sent by A
    int numRetransmissions_A;   //number of retransmissions from A
    int numAcksReceived_A;  //number of acks that A receives from B
    Vector<Packet> outstandingPackets;   //vector to show current outstanding packets
    int nextSeqnum; //the next open sequence number
    Vector<Packet> outputBuffer;   //holds messages to send
    int outputBufferMax;    //the max size of the sender's output buffer
    int numCorruptAcks_A;   //the number of corrupted acks A receives
    int sendWindowHead;     //the first sequence number in A's send window

    //side B class variables:
    int numLayer5Deliveries_B;  //number of packets delivered to layer 5 of B
    int numAcksSent_B;  //number of ACK messages sent by B
    Vector<Packet> inputBuffer; //holds out-of-order but valid packets received by B
    int recvWindowHead;     //the first sequence number in B's receive window
    int lastAcked;      //the last sequence number B acked
    int numCorruptMsgs_B;   //the number of corrupted messages B receives

    //general class variables
    int numCorruptPackets;  //total number of corrupted packets encountered
    int seqForRTT;  //the sequence number of the packet being used for current RTT measurement
    int numRTTs;    //total number of valid RTTs measured
    double RTTSum;     //the sum of all RTTs measured; used with numRTTs to find average
    double RTTStartTime;  //the start of the RTT being tracked
    int seqForComms;    //the sequence number of the packet being used for current comms measurement
    int numComms;   //total number of communications
    double commsSum;  //the sume of all comms meeasured; also used to find average
    double commsStartTime;    //the start of the communication being tracked
    int numUnbufferedMsgs;  //the number of messages dropped due to a full send buffer. Ideally 0
    int numBufferedMsgs;    //the number of messages sent to the output buffer

    //general class methods
    //returns ratio of lost packets
    private double lostPacketRatio() {
        return
                (double) Math.max(0, numRetransmissions_A - numCorruptPackets)
                        / ((numTransmittedPackets_A + numRetransmissions_A) + numAcksSent_B);
    }

    //returns ratio of corrupted packets
    private double corruptPacketRatio() {
        return
                (double) numCorruptPackets
                        / ((numTransmittedPackets_A + numRetransmissions_A) + numAcksSent_B
                        - (numRetransmissions_A - numCorruptPackets));
    }

    //helper method, calculates a checksum to add to a message header
    private int createChecksum(String payload, int seqnum, int acknum){
        //corruption is only applied to the message string, seqnum, and acknum in this code, so the checksum
        // will only account for these.
        //This method uses the 1s complement checksum with the bits of the characters in the string
        int sum = 0;
        //add string chars
        for (char c : payload.toCharArray()) {
            sum += c;              //add the int value of the character
            sum = (sum & 0xFFFF) + (sum >> 16);  //remove overflow bits and add them back to the sum
        }
        //add seqnum in two halves of 16 bits each
        sum += seqnum & 0xFFFF; //add lower half
        sum = (sum & 0xFFFF) + (sum >> 16); //add back overflow
        sum += (seqnum >> 16) & 0xFFFF; //add upper half
        sum = (sum & 0xFFFF) + (sum >> 16); //add back overflow
        //add acknum in two halves
        sum += acknum & 0xFFFF; //add lower half
        sum = (sum & 0xFFFF) + (sum >> 16); //add back overflow
        sum += (acknum >> 16) & 0xFFFF; //add upper half
        sum = (sum & 0xFFFF) + (sum >> 16); //add back overflow

        //do NOT invert the bits here. Having a non-inverted version is useful for verifying
        // the checksum later.
        return sum;
    }

    //gets checksum and adds it to given packet
    // In this code, the checksum is NOT optional so no extra steps are needed to handle all-0s checksums
    private void addChecksum(Packet packet){
        int checksum = createChecksum(packet.getPayload(), packet.getSeqnum(), packet.getAcknum());
        checksum ^= 0xFFFF;    //invert bits
        packet.setChecksum(checksum);
    }

    //verifies the checksum of a received message
    private boolean verifyChecksum(Packet packet){
        //Since the checksum is generated with 1s complement and the bits of the packet header,
        // it is verified in the same way.
        int checksum = createChecksum(packet.getPayload(), packet.getSeqnum(), packet.getAcknum());
        checksum += packet.getChecksum();
        checksum = (checksum & 0xFFFF) + (checksum >> 16);
        checksum ^= 0xFFFF;   //invert bits
        return checksum == 0;
    }

    // This is the constructor.  Don't touch!
    public StudentNetworkSimulator(int numMessages,
                                   double loss,
                                   double corrupt,
                                   double avgDelay,
                                   int trace,
                                   int seed,
                                   int winsize,
                                   double delay)
    {
        super(numMessages, loss, corrupt, avgDelay, trace, seed);
	WindowSize = winsize;
	LimitSeqNo = winsize*2; // set appropriately; assumes SR here!
	RxmtInterval = delay;
    }


    //helper function to check if a given sequence number is in a send/receive window.
    //included for a simpler interface
    protected boolean isInWin(int seqNum, int leftSide, int windowSize) {
        return isBetween(seqNum, leftSide, (leftSide + windowSize - 1) % LimitSeqNo);
    }

    //helper function to handle general number range checks
    private boolean isBetween(int seqNum, int start, int end) {
        if (start <= end) {
            return seqNum >= start && seqNum <= end;
        } else { //the range wraps around
            return seqNum >= start || seqNum <= end;
        }
    }


    // This routine will be called whenever the upper layer at the sender [A]
    // has a message to send.  It is the job of your protocol to insure that
    // the data in such a message is delivered in-order, and correctly, to
    // the receiving upper layer.
    protected void aOutput(Message message)
    {
        //create new packet; ack num is arbitrary and checksum starts empty
        Packet newPacket = new Packet(-1, -1, 0, message.getData());
        //check if there are already max # of outstanding packets or if the next sequence number
        // will be outside the send window.
        if(outstandingPackets.size() >= WindowSize || !isInWin(nextSeqnum, sendWindowHead, WindowSize)) {
            //if the buffer is not full, buffer. Else, toss out packet as per assignment instructions
            if (outputBuffer.size() < outputBufferMax) {
                outputBuffer.add(newPacket);
                numBufferedMsgs++;
            } else {
                //ELSE: do nothing, let function end
                System.out.println("BUFFER FULL: dropping message " + message.getData());
                numUnbufferedMsgs++;
                return;
            }
        }
        else {
            //Apply a sequence number and checksum only once the packet is actually sent
            newPacket.setSeqnum(nextSeqnum);
            addChecksum(newPacket);
            nextSeqnum = (nextSeqnum + 1) % LimitSeqNo; //increment seqnum, wrap if needed
            //restart the timer on sending the packet
            stopTimer(A);
            toLayer3(A, newPacket);
            startTimer(A, RxmtInterval);

            //Start tracking the comms and RTT time for this packet
            if(seqForRTT == -1){
                seqForRTT = newPacket.getSeqnum();
                RTTStartTime = getTime();
            }
            if(seqForComms == -1){
                seqForComms = newPacket.getSeqnum();
                commsStartTime = getTime();
            }


            numTransmittedPackets_A++;
            outstandingPackets.add(newPacket);
        }
    }

    //helper function to handle retransmitting oldest outstanding packet, which happens at several points in A
    protected void aRetransmitOutstandingPacket() {
        Packet p = outstandingPackets.get(0);
        System.out.println("RETRANSMITTING NUMBER " + p.getSeqnum());
        //restart timer and retransmit
        stopTimer(A);
        toLayer3(A, p);
        startTimer(A, RxmtInterval);
        //Cancel RTT measurement for the retransmitted packet if it is being measured
        if(p.getSeqnum() == seqForRTT){
            seqForRTT = -1;
        }
        numRetransmissions_A++;
    }

    // This routine will be called whenever a packet sent from the B-side 
    // (i.e. as a result of a toLayer3() being done by a B-side procedure)
    // arrives at the A-side.  "packet" is the (possibly corrupted) packet
    // sent from the B-side.
    protected void aInput(Packet packet)
    {
        //first, calculate the checksum to verify that the message is not corrupted
        //if the checksum is bad, retransmit the oldest outstanding packet
        if(!verifyChecksum(packet)){
            numCorruptPackets++;
            numCorruptAcks_A++;
            return;
        }
        //If it's valid, then regardless of if it is a duplicate or not this ack should be tallied
        numAcksReceived_A++;
        //check if this ack has already been processed (check if it is a duplicate)
        // by checking if the packet it acks is still outstanding
        boolean duplicate = true;
        Packet acked = null;
        for(Packet p : outstandingPackets){
            if(p.getSeqnum() == packet.getAcknum()) {
                acked = p;
                duplicate = false;
                break;
            }
        }
        //if the corresponding outstanding packet is not found, the ack must be a duplicate.
        //As per instructions, on duplicate ack reception, retransmit the oldest outstanding packet
        if(duplicate && !outstandingPackets.isEmpty()){ //of course, nothing can be retransmitted if nothing is outstanding
            System.out.println("A GOT DUP ACK " + packet.getAcknum() + " AT TIME " + getTime());
            aRetransmitOutstandingPacket();
        }
        //Else, adjust send buffer as needed and, if possible, send new packet
        else if(!duplicate) {
            //in this version of SR, stop the timer whenever a new valid ack arrives.
            stopTimer(A);

            //get and record the RTT and comms time
            if(packet.getAcknum() == seqForRTT){
                numRTTs++;
                RTTSum += getTime() - RTTStartTime;
                seqForRTT = -1;
            }
            if(packet.getAcknum() == seqForComms){
                numComms++;
                commsSum += getTime() - commsStartTime;
                seqForComms = -1;
            }

            //remove the acked packet
            outstandingPackets.remove(acked);
            //Since this protocol is cumack, also remove outstanding packets that implicitly have been
            // acked
            Vector<Packet> packetsToRemove = new Vector<>();
            for(Packet p : outstandingPackets){
                //for each outstanding packet, check if it is between the current send window
                // head and the newest cumack inclusive
                if(isBetween(p.getSeqnum(), sendWindowHead, packet.getAcknum())) {
                    packetsToRemove.add(p);
                    //Since the packet is being acked, we should make sure to cancel the time measurements
                    // if necessary
                    if(p.getSeqnum() == seqForRTT){
                        numRTTs++;
                        RTTSum += getTime() - RTTStartTime;
                        seqForRTT = -1;
                    }
                    if(p.getSeqnum() == seqForComms){
                        numComms++;
                        commsSum += getTime() - commsStartTime;
                        seqForComms = -1;
                    }
                }
            }
            for(Packet p : packetsToRemove){outstandingPackets.remove(p);}

            //Since this implementation uses cumack, any valid new ack should update the left side
            // of the send window
            int oldHead = sendWindowHead;   //store for printing purposes
            sendWindowHead = (packet.getAcknum() + 1) % LimitSeqNo;

            System.out.println(
                    "ACK " + packet.getAcknum() + " RECEIVED, TRYING TO SEND BUFFERED PACKET: "
                    + "\nO. Packets size: " + outstandingPackets.size()
                            + "\nWin. size: " + WindowSize
                    + "\nOutput Buffer size: " + outputBuffer.size()
                    + "\nTime: " + getTime()
            );
            System.out.println("SEND WINDOW HEAD SHIFTED FROM " + oldHead + " TO " + sendWindowHead);
            //fill send window with new packets from buffer
            while(outstandingPackets.size() < WindowSize && !outputBuffer.isEmpty()) {
                Packet newPacket = outputBuffer.remove(0);
                newPacket.setSeqnum(nextSeqnum);
                addChecksum(newPacket);
                nextSeqnum = (nextSeqnum + 1) % LimitSeqNo;
                stopTimer(A);
                toLayer3(A, newPacket);
                startTimer(A, RxmtInterval);

                //start new RTT and comms measurement if one is not running
                if(seqForRTT == -1){
                    seqForRTT = newPacket.getSeqnum();
                    RTTStartTime = getTime();
                }
                if(seqForComms == -1){
                    seqForComms = newPacket.getSeqnum();
                    commsStartTime = getTime();
                }

                outstandingPackets.add(newPacket);
                numTransmittedPackets_A++;
            }
        }
    }
    
    // This routine will be called when A's timer expires (thus generating a 
    // timer interrupt). You'll probably want to use this routine to control 
    // the retransmission of packets. See startTimer() and stopTimer(), above,
    // for how the timer is started and stopped. 
    protected void aTimerInterrupt()
    {
        //Find the oldest outstanding packet and retransmit it, then start the timer again.
        //this vector is LIFO, with newer packets being added to the end. The first packet in
        // the vector can therefore be considered the oldest.
        System.out.println("TIMEOUT AT TIME " + getTime());
        if(!outstandingPackets.isEmpty()) {
            aRetransmitOutstandingPacket();
        }
    }
    
    // This routine will be called once, before any of your other A-side 
    // routines are called. It can be used to do any required
    // initialization (e.g. of member variables you add to control the state
    // of entity A).
    protected void aInit()
    {
        numTransmittedPackets_A = 0;
        numRetransmissions_A = 0;
        numCorruptPackets = 0;
        numAcksReceived_A = 0;
        outstandingPackets = new Vector<>();
        nextSeqnum = FirstSeqNo;
        outputBuffer = new Vector<>();
        outputBufferMax = 100; //LimitSeqNo;
        numCorruptAcks_A = 0;
        sendWindowHead = FirstSeqNo;

        numComms = 0;
        numRTTs = 0;
        commsSum = 0;
        RTTSum = 0;
        seqForComms = -1;
        seqForRTT = -1;
        numUnbufferedMsgs = 0;
    }

    //A helper function to handle the cumack retransmission sequence that happens at a few points
    protected void bRetransmitCumack() {
        Packet newAck = new Packet(-1, lastAcked, 0, "");
        addChecksum(newAck);
        toLayer3(B, newAck);
        numAcksSent_B++;
    }

    // This routine will be called whenever a packet sent from the B-side 
    // (i.e. as a result of a toLayer3() being done by an A-side procedure)
    // arrives at the B-side.  "packet" is the (possibly corrupted) packet
    // sent from the A-side.
    protected void bInput(Packet packet)
    {
        //Check for corruption. If corrupted, ignore it.
        if(!verifyChecksum(packet)){
            System.out.println("----------------B found invalid checksum");
            numCorruptPackets++;
            numCorruptMsgs_B++;
            return;
        }

        //check if packet is within the allowed range for the current receive window
        if(!isInWin(packet.getSeqnum(), recvWindowHead, WindowSize)) {
            System.out.println("B found seqnum " + packet.getSeqnum()
                    + " but it was not in rwin [" + recvWindowHead + ", "
                    + ((recvWindowHead+WindowSize-1)%LimitSeqNo)+"]");
            bRetransmitCumack();
            return; //ignore the packet if it is not in the receive window
        }

        //check for a duplicate by checking if this packet is in the current
        // input buffer. If it already is there, ignore it but send a cumack again.
        for(Packet p : inputBuffer){
            if(p.getSeqnum() == packet.getSeqnum()) {
                bRetransmitCumack();
                //System.out.println("B found duplicate");
                return;
            }
        }

        //If this packet is at the head of the receive window, all subsequent buffered packets need to also
        // be consumed and the receive window needs to shift with them.
        //Repeatedly check the input buffer for the next packet in line, consuming it and shifting the
        // send window when it is found and stopping when it is not found. At the end, ack the last
        // consumed packet as a cumack for all of them.
        if(packet.getSeqnum() == recvWindowHead) {
            toLayer5(packet.getPayload());
            numLayer5Deliveries_B++;
            recvWindowHead = (recvWindowHead + 1) % LimitSeqNo;
            int currNum = packet.getSeqnum();
            boolean keepChecking = true;
            Vector<Packet> packetsToRemove = new Vector<>();
            while (keepChecking) {
                keepChecking = false;
                int nextNum = (currNum + 1) % LimitSeqNo;
                for (Packet p : inputBuffer) {
                    if (p.getSeqnum() == nextNum) {
                        if (p.getSeqnum() == recvWindowHead) {
                            recvWindowHead = (recvWindowHead + 1) % LimitSeqNo;
                        }
                        keepChecking = true;
                        currNum = nextNum;
                        toLayer5(p.getPayload());
                        numLayer5Deliveries_B++;
                        packetsToRemove.add(p);
                        break;
                    }
                }
            }
            for(Packet p : packetsToRemove) {inputBuffer.remove(p);}
            Packet newAck = new Packet(-1, currNum, 0, "");
            addChecksum(newAck);
            toLayer3(B, newAck);
            numAcksSent_B++;
            lastAcked = currNum;

            return;
        }

        //Finally, if none of the other cases apply then this is a valid out-of-order packet.
        // Just buffer it and make sure to send a cumack.
        //Note: this may ack with a number different from what was received on account of the cumack.
        // It's different from the SR we saw in class but it's expected for this assignment.
        inputBuffer.add(packet);
        Packet anotherAck = new Packet(-1, lastAcked, 0, "");
        addChecksum(anotherAck);
        toLayer3(B, anotherAck);
        numAcksSent_B++;
    }
    
    // This routine will be called once, before any of your other B-side 
    // routines are called. It can be used to do any required
    // initialization (e.g. of member variables you add to control the state
    // of entity B).
    protected void bInit()
    {
        numAcksSent_B = 0;
        numLayer5Deliveries_B = 0;
        inputBuffer = new Vector<>();
        recvWindowHead = FirstSeqNo;
        //when the program starts, nothing has been acked so cumacking OOO packets is awkward.
        //for now, set it to be the last sequence number before wrapping to 0.
        lastAcked = (FirstSeqNo - 1 + LimitSeqNo) % LimitSeqNo;
    }

    // Use to print final statistics
    protected void Simulation_done()
    {
    	// TO PRINT THE STATISTICS, FILL IN THE DETAILS BY PUTTING VARIBALE NAMES. DO NOT CHANGE THE FORMAT OF PRINTED OUTPUT
    	System.out.println("\n\n===============STATISTICS=======================");
    	System.out.println("Number of original packets transmitted by A: " + numTransmittedPackets_A);
    	System.out.println("Number of retransmissions by A: " + numRetransmissions_A);
    	System.out.println("Number of data packets delivered to layer 5 at B: " + numLayer5Deliveries_B);
    	System.out.println("Number of ACK packets sent by B: " + numAcksSent_B);
    	System.out.println("Number of corrupted packets: " + numCorruptPackets);
    	System.out.println("Ratio of lost packets: " + lostPacketRatio());
    	System.out.println("Ratio of corrupted packets: " + corruptPacketRatio());
    	System.out.println("Average RTT: " + RTTSum/numRTTs);
    	System.out.println("Average communication time: " + commsSum/numComms);
    	System.out.println("==================================================");

    	// PRINT YOUR OWN STATISTIC HERE TO CHECK THE CORRECTNESS OF YOUR PROGRAM
    	System.out.println("\nEXTRA:");
    	System.out.println("Number of ACK packets received by A: " + numAcksReceived_A);
        System.out.println("Number of corrupted acks received by A: " + numCorruptAcks_A);
        System.out.println("Number of corrupted messages received by B: " + numCorruptMsgs_B);
        System.out.println("Number of packets dropped due to full send buffer: " + numUnbufferedMsgs);
        System.out.println("Number of packets sent to output buffer by A: " + numBufferedMsgs);
    }

    //returns time stats to be used in data compilation
    public double[] getTimeStats() {
        //return: average RTT, average comm, total retransmissions
        return new double[] {RTTSum/numRTTs, commsSum/numComms, numRetransmissions_A};
    }

}

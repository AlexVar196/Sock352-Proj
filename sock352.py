#This is lightly edited code from Anarav Patel and Saurin Shah
import binascii
import base64
import threading
import wrapper as syssock
import struct
import sys
import time
from random import randint
# encryption libraries
import nacl.secret
import nacl.public
import nacl.utils
import nacl.pwhash

from nacl.public import PrivateKey, Box

#Global variables that store the sending and receiving ports of the socket
portTx = 0
portRx = 0

#Global variables that store the packet header format and packet header length
#to use within the struct in order to pack and unpack
PACKET_HEADER_FORMAT = "!BBBBHHLLQQLL"
PACKET_HEADER_LENGTH = struct.calcsize(PACKET_HEADER_FORMAT)

#Global variables that are responsible for storing the maximum packet size and
#the
#maximum payload size
MAXIMUM_PACKET_SIZE = 4048
#64000
MAXIMUM_PAYLOAD_SIZE = MAXIMUM_PACKET_SIZE - PACKET_HEADER_LENGTH

#Global variables that define all the packet bits
SOCK352_SYN = 0x01
SOCK352_FIN = 0x02
SOCK352_ACK = 0x04
SOCK352_RESET = 0x08
SOCK352_HAS_OPT = 0x10
SECURE_HDR_SIZE = 40

#Global variables that store the index for the flag, sequence no.  and ack no.
#within the packet header
PACKET_FLAG_INDEX = 1
PACKET_SEQUENCE_NO_INDEX = 8
PACKET_ACK_NO_INDEX = 9
WINDOW_NO_INDEX = 10

START_CONG_PACKETS_NUMER = 2

#String message to print out that a connection has been already established
CONNECTION_ALREADY_ESTABLISHED_MESSAGE = "This socket supports a maximum of one connection\n" \
                                 "And a connection is already established"

# the public and private keychains in hex format
global publicKeysHex
global privateKeysHex

# the public and private keychains in binary format
global publicKeys
global privateKeys

global recv_data_thread

# the encryption flag
global ENCRYPT
ENCRYPT = 236

global WINDOW_SIZE
WINDOW_SIZE = 32768
publicKeysHex = {} 
privateKeysHex = {} 
publicKeys = {} 
privateKeys = {}

def init(UDPportTx, UDPportRx):
    # Sets the transmit port to 27182 (default) if its None or 0
    if (UDPportTx is None or UDPportTx == 0):
        UDPportTx = 27182

    # Sets the receive port to 27182 (default) if its None or 0
    if (UDPportRx is None or UDPportRx == 0):
        UDPportRx = 27182

    # Assigns the global transmit and receive ports to be the one passed in
    # through this method
    global portTx, portRx
    portTx = int(UDPportTx)
    portRx = int(UDPportRx)

# read the keyfile.  The result should be a private key and a keychain of
# public keys
def readKeyChain(filename):
    global publicKeysHex
    global privateKeysHex 
    global publicKeys
    global privateKeys 
    
    if (filename):
        try:
            keyfile_fd = open(filename,"r")
            for line in keyfile_fd:
                words = line.split()
                # check if a comment
                # more than 2 words, and the first word does not have a
                # hash, we may have a valid host/key pair in the keychain
                if ((len(words) >= 4) and (words[0].find("#") == -1)):
                    host = words[1]
                    if(words[2] == '*'):
                        port = 0
                    else:
                        port = int(words[2])
                    keyInHex = words[3]
                    if (words[0] == "private"):
                        privateKeysHex[(host,port)] = keyInHex
                        privateKeys[(host,port)] = nacl.public.PrivateKey(keyInHex, nacl.encoding.HexEncoder)
                    elif (words[0] == "public"):
                        publicKeysHex[(host,port)] = keyInHex
                        publicKeys[(host,port)] = nacl.public.PublicKey(keyInHex, nacl.encoding.HexEncoder)
        except Exception,e:
            print ("error: opening keychain file: %s %s" % (filename,repr(e)))
    else:
            print ("error: No filename presented")             

    return (publicKeys,privateKeys)


class socket:

    # initializes the socket by setting various class specific variables
    def __init__(self):

        self.recv_data_not_started = True

        self.window_buffer = bytearray(WINDOW_SIZE)
        self.window = WINDOW_SIZE
        self.window_buffer_data_offset = 0
                
        self.window_buffer_lock = threading.Lock()

        # creates the socket
        self.socket = syssock.socket(syssock.AF_INET, syssock.SOCK_DGRAM)

        # sets the timeout to be 0.2 seconds
        self.socket.settimeout(0.2)

        # sets the send address to be None (to be initialized later)
        self.send_address = None

        # sets the boolean for whether or not the socket is connected
        self.is_connected = False

        # controls whether or not this socket can close (it's only allowed to
        # close once all data is received)
        self.can_close = False

        self.closing = False

        self.reset = False

        self.dropped_rx_packets = 0

        # selects a random sequence number between 1 and 100000 as the first
        # sequence number
        self.sequence_no = randint(1, 100000)

        # sets the ack number of the socket to be 0, inititalized later when
        # connection is established
        self.ack_no = 0

        # declares the data packets array, for the sender its the packets it
        # sends and for the receiver, its the
        # packets it has received
        self.data_packets = []

        # declares the file length, which will set later (in send by the client
        # and in recv by the server)
        self.file_len = -1

        # declares the retransmit boolean which represents whether or not to
        # resend packets and Go-Back-N
        self.retransmit = False

        # the corresponding lock for the retransmit boolean
        self.retransmit_lock = threading.Lock()

        # declares the last packet that was acked (for the sender only)
        self.last_data_packet_acked = None

        self.rx_box = None
        self.socket_box = None

        self.encrypt = False
        self.nonce = None

        self.fin_received = False

    def get_window_size(self):
        self.window_buffer_lock.acquire()
        window = self.window
        self.window_buffer_lock.release()
        return window

    def set_window_size(self, window):
        self.window_buffer_lock.acquire()
        self.window = window
        self.window_buffer_lock.release()

    def insert_received_data(self, data, data_len):
        #self.window_buffer
        out_len = 0
        self.window_buffer_lock.acquire() 
        if self.window >= data_len:
           #we have enough room to copy data
           self.window_buffer[WINDOW_SIZE - self.window:] = data[:data_len]
           out_len = data_len
           self.window -= out_len
           #print "Insert data: ", out_len, " window: ", self.window
        else:
            print "Widow is too small for new data: ", self.window

        self.window_buffer_lock.release()
        return out_len

    def extract_requested_data(self, data_len):
        #print "Data requested ", data_len
        self.window_buffer_lock.acquire() 
        window_buffer_data_len = WINDOW_SIZE - self.window
        #print "Current window_buffer_data_len ", window_buffer_data_len
        out_data_len = min(data_len, window_buffer_data_len)
        #print "Data to extract ", out_data_len
        out_data = self.window_buffer[: out_data_len]
        #move data to the begenning of the window buffer
        if window_buffer_data_len > out_data_len:
            temp_window_buffer = bytearray(WINDOW_SIZE)
            temp_window_buffer[:] = self.window_buffer[out_data_len : window_buffer_data_len]
            window_buffer_data_len -= out_data_len
            self.window_buffer = temp_window_buffer[:window_buffer_data_len]
            self.window = WINDOW_SIZE - window_buffer_data_len
        else:
            self.window = WINDOW_SIZE

        #print "New window_buffer_data_len ", window_buffer_data_len, "Window: ", self.window

        self.window_buffer_lock.release()
        return out_data, out_data_len

    # binds the server to the receiving port
    def bind(self, address):
        print "Listen on: ", (address[0], portRx)
        self.socket.bind((address[0], portRx))


    # client's method to establish a connection
    def connect(self, *args):
        global sock352portTx
        global ENCRYPT
        global tx_box
        # sets the send address to the tuple (address ip, transmit port)

        if (len(args) >= 1): 
            self.send_address = args[0]
            self.send_address = (self.send_address[0], portTx)
        if (len(args) >= 2):
            if(args[1] == ENCRYPT):
                self.encrypt = True
                self.nonce = nacl.utils.random(nacl.secret.SecretBox.NONCE_SIZE)
                self.socket_box = Box(privateKeys.get(('*', 0)), publicKeys.get(self.send_address))
            else:
                 raise Exception('Error! Bad argument args[1]')


        self.send_address = (self.send_address[0], portTx)

        # binds the client on the receiving port
        self.socket.bind((self.send_address[0], portRx))

        # makes sure the client isn't already connected.  If it is, prints an
        # error message
        if self.is_connected:
            print (CONNECTION_ALREADY_ESTABLISHED_MESSAGE)
            return
        
        # Step 1: Request to connect to the server by setting the SYN flag
        # first the packet is created using createPacket and passing in the
        # apprpriate variables
        syn_packet = self.createPacket(flags=SOCK352_SYN, sequence_no=self.sequence_no)
        self.sendto_encrypted(syn_packet, self.send_address)
        # increments the sequence since it was consumed in creation of the SYN
        # packet
        self.sequence_no += 1

        # Receives the SYN_ACK from Step 2 within accept()
        
        received_handshake_packet = False
        while not received_handshake_packet:
            try:
                # tries to receive a SYN/ACK packet from the server using
                # self.recv_encrypted and unpacks it
                (syn_ack_packet, addr) = self.recvfrom_decrypted() 
                syn_ack_packet = struct.unpack(PACKET_HEADER_FORMAT, syn_ack_packet)
                # if it receives a reset marked flag for any reason, abort the
                # handshake
                if syn_ack_packet[PACKET_FLAG_INDEX] == SOCK352_RESET:
                    print "Connection was reset by the server"
                    return

                # if it receives a packet, and it is SYN/ACK, we are done
                if syn_ack_packet[PACKET_FLAG_INDEX] == SOCK352_SYN | SOCK352_ACK:
                    received_handshake_packet = True

                # if it receives a packet with an incorrect ACK from its
                # sequence number,
                # it tries to receive more packets
                if syn_ack_packet[PACKET_ACK_NO_INDEX] != self.sequence_no:
                    received_handshake_packet = False
            # retransmits the SYN packet in case of timeout when receiving a
            # SYN/ACK from the server
            except syssock.timeout:
                self.sendto_encrypted(syn_packet, self.send_address)

        # sets the client's acknowledgement number to be SYN/ACK packet's
        # sequence number + 1
        self.ack_no = syn_ack_packet[PACKET_SEQUENCE_NO_INDEX] + 1

        # Step 3: Send a packet with the ACK flag set to acknowledge the
        # SYN/ACK packet
        ack_packet = self.createPacket(flags=SOCK352_ACK,
                                       sequence_no=self.sequence_no,
                                       ack_no=self.ack_no)
        # increments the sequence number as it was consumed by the ACK packet
        self.sequence_no += 1

        # sets the connected boolean to be true
        self.is_connected = True

        # sends the ack packet to the server, as it assumes it's connected now
        self.sendto_encrypted(ack_packet, self.send_address)
        print ("Client is now connected to the server at %s:%s" % (self.send_address[0], self.send_address[1]))

    # does nothing so far
    def listen(self, backlog):
        return

    # server code for establishing the connection
    def accept(self,*args):

        # example code to parse an argument list (use option arguments if you
        # want)
        global ENCRYPT
        if(len(args) >= 1):
            if (args[0] == ENCRYPT):
                self.encrypt = True

        # makes sure again that the server is not already connected
        # because part 1 supports a single connection only
        if self.is_connected:
            print (CONNECTION_ALREADY_ESTABLISHED_MESSAGE)
            return

        # Keeps trying to receive the request to connect from a potential
        # client until we get a connection request
        got_connection_request = False
        while not got_connection_request:
            try:
                self.socket.settimeout(None)
                # tries to receive a potential SYN packet and unpacks it
                (syn_packet, addr) = self.recvfrom_decrypted()
                syn_packet = struct.unpack(PACKET_HEADER_FORMAT, syn_packet)

                print "Connection request from: ", addr

                # if the received packet is not a SYN packet, it ignores the
                # packet
                if syn_packet[PACKET_FLAG_INDEX] == SOCK352_SYN:
                    got_connection_request = True
            # if the receive times out while receiving a SYN packet, it tries
            # to listen again
            except syssock.timeout:
                pass

        # Step 2: Send a SYN/ACK packet for the 3-way handshake
        # creates the flags bit to be the bit-wise OR of SYN/ACK
        flags = SOCK352_SYN | SOCK352_ACK
        # creates the SYN/ACK packet to ACK the connection request from client
        # and sends the SYN to establish the connection from this end
        syn_ack_packet = self.createPacket(flags=flags,
                                           sequence_no=self.sequence_no,
                                           ack_no=syn_packet[PACKET_SEQUENCE_NO_INDEX] + 1)
        # increments the sequence number as it just consumed it when creating
        # the SYN/ACK packet
        self.sequence_no += 1
        # sends the created packet to the address from which it received the
        # SYN packet
        self.sendto_encrypted(syn_ack_packet, addr)

        # Receive the final ACK to complete the handshake and establish
        # connection
        got_final_ack = False
        while not got_final_ack:
            try:
                # keeps trying to receive the final ACK packet to finalize the
                # connection
                (ack_packet, addr) = self.recvfrom_decrypted()
                        # updates the server's send address
                self.send_address = (addr[0], portTx)

                ack_packet = struct.unpack(PACKET_HEADER_FORMAT, ack_packet)
                # if the unpacked packet has the ACK flag set, we are done
                if ack_packet[PACKET_FLAG_INDEX] == SOCK352_ACK:
                    got_final_ack = True
            # if the server times out when trying to receive the final ACK, it
            # retransmits the SYN/ACK packet
            except syssock.timeout:
                self.sendto_encrypted(syn_ack_packet, addr)

        # updates the server's ack number to be the last packet's sequence
        # number + 1
        self.ack_no = ack_packet[PACKET_SEQUENCE_NO_INDEX] + 1


        # connect to the client using the send address just set
        #self.socket.connect(self.send_address)

        # updates the connected boolean to reflect that the server is now
        # connected
        self.is_connected = True

        print("Server is now connected to the client at %s:%s" % (self.send_address[0], self.send_address[1]))

        return self, addr


    def close_and_cleanup(self):

        # calls the socket's close method to finally close the connection
        self.socket.close()
        # resets all the appropriate variables
        self.send_address = None
        self.is_connected = False
        self.can_close = False
        self.sequence_no = randint(1, 100000)
        self.ack_no = 0
        self.data_packets = []
        self.file_len = -1
        self.retransmit = False
        self.last_data_packet_acked = None


    # handles closing the connection for both server and client
    def close(self):
        # makes sure there is a connection established in the first place
        # before trying to close it
        if not self.is_connected:
            print ("No connection is currently established that can be closed")
            return

        packet = ''
        # checks if the server can close the connection (it can close only when
        # it has received the last packet/ack)
        if self.can_close == True:
            if self.fin_received == False:
                packet = self.createPacket(flags=SOCK352_FIN,
                                       sequence_no=self.sequence_no,
                                       ack_no=self.ack_no)
                self.sequence_no += 1
                # the server sends the packet to ACK the data packet it
                # received
                self.sendto_encrypted(packet, self.send_address)

                try:
                    disconection_finished = False
                    while not disconection_finished:
                        # wait 5 sec
                        self.socket.settimeout(5)
                        print "Disconnecting..."

                        new_packet = self.recv_decrypted()
                        
                        # filter out not control packets.  That might be packets
                        # retransmitted by peer
                        if len(new_packet) == SECURE_HDR_SIZE:
                            new_packet = struct.unpack(PACKET_HEADER_FORMAT, new_packet)
                            self.ack_no += 1
                            if new_packet[PACKET_FLAG_INDEX] == SOCK352_FIN and self.fin_received == False:
                                # Received SOCK352_FIN. Closing connection Gracefully
                                self.fin_received = True
                                #respond with ACK
                                packet = self.createPacket(flags=SOCK352_ACK,
                                           sequence_no=self.sequence_no,
                                           ack_no=self.ack_no)
                                self.sequence_no += 1
                                self.sendto_encrypted(packet, self.send_address)
                            elif new_packet[PACKET_FLAG_INDEX] == SOCK352_ACK:
                                disconection_finished = True
                                # Disconnection Confirmed by peer
                                return
                        else:
                            packet_header = new_packet[:SECURE_HDR_SIZE]
                            packet_header = struct.unpack(PACKET_HEADER_FORMAT, packet_header)
                            self.ack_no += 1
                            packet = self.createPacket(flags=SOCK352_ACK,
                                           sequence_no=self.sequence_no,
                                           ack_no=self.ack_no)
                            self.sequence_no += 1
                            self.sendto_encrypted(packet, self.send_address)
                except syssock.timeout:
                    # FIN receive timeout. close connection. can terminate
                    self.close_and_cleanup()
                    return
            else:
                try:
                    #respond with ACK
                    packet = self.createPacket(flags=SOCK352_ACK,
                                           sequence_no=self.sequence_no,
                                           ack_no=self.ack_no)
                    self.sequence_no += 1
                    self.sendto_encrypted(packet, self.send_address)
                    #send FIN
                    packet = self.createPacket(flags=SOCK352_FIN,
                                       sequence_no=self.sequence_no,
                                       ack_no=self.ack_no)
                    self.sequence_no += 1
                    self.sendto_encrypted(packet, self.send_address)
                    
                    disconection_finished = False
                    while not disconection_finished:
                        # wait 5 sec
                        self.socket.settimeout(5)
                        print "Disconnecting... FIN received"
                        new_packet = self.recv_decrypted()
                        packet_header = new_packet[:SECURE_HDR_SIZE]
                        # filter out not control packets.  That might be packets
                        # retransmitted by peer
                        if len(new_packet) == SECURE_HDR_SIZE:
                            new_packet = struct.unpack(PACKET_HEADER_FORMAT, new_packet)
                            if new_packet[PACKET_FLAG_INDEX] == SOCK352_ACK:
                                disconection_finished = True
                                self.close_and_cleanup()
                                return
                        else:
                            packet_header = new_packet[:SECURE_HDR_SIZE]
                            packet_header = struct.unpack(PACKET_HEADER_FORMAT, packet_header)
                            self.ack_no += 1
                            packet = self.createPacket(flags=SOCK352_ACK,
                                           sequence_no=self.sequence_no,
                                           ack_no=self.ack_no)
                            self.sequence_no += 1
                            self.sendto_encrypted(packet, self.send_address)
                except syssock.timeout:
                    # ACK receive timeout. close connection. can terminate
                    self.close_and_cleanup()
                    return

        #print "Not ready to close"


    # method responsible for breaking apart the buffer into chunks of maximum
    # payload length
    def create_data_packets(self, buffer):

        if(self.encrypt == True):
            #adjust max payload len for encrypted buffer which is double of the
            #original size
            practical_max_payload_size = MAXIMUM_PAYLOAD_SIZE - SECURE_HDR_SIZE
        else:
            practical_max_payload_size = MAXIMUM_PAYLOAD_SIZE

        # calculates the total packets needed to transmit the entire buffer
        total_packets = len(buffer) / practical_max_payload_size

        # if the length of the buffer is not divisible by the maximum payload
        # size,
        # that means an extra packet will need to be sent to transmit the left
        # over data
        # so it increments total packets by 1
        if len(buffer) % practical_max_payload_size != 0:
            total_packets += 1

        # sets the payload length to be the maximum payload size
        payload_len = practical_max_payload_size

        # iterates up to total packets and creates each packet
        for i in range(0, total_packets):
            # if we are about to construct the last packet, checks if the
            # payload length
            # needs to adjust to reflect the left over size or the entire
            # maximum packet size
            if i == total_packets - 1:
                if len(buffer) % practical_max_payload_size != 0:
                    payload_len = len(buffer) % practical_max_payload_size

            # creates the new packet with the appropriate header
            new_packet = self.createPacket(flags=SOCK352_ACK,
                                           sequence_no=self.sequence_no,
                                           ack_no=self.ack_no,
                                           payload_len=payload_len)
            # consume the sequence and ack no as it was used to create the
            # packet
            self.sequence_no += 1
            self.ack_no += 1

            # attaches the payload length of buffer to the end of the header to
            # finish constructing the packet
            self.data_packets.append(new_packet + buffer[practical_max_payload_size * i:
                                                         practical_max_payload_size * i + payload_len])
        return total_packets

    # method responsible for sending data packets (used by the sender)
    def send(self, buffer):
        # makes sure that the file length is set and has been communicated to
        # the receiver
        if self.file_len == - 1:
            self.sendto_encrypted(buffer, self.send_address)
            self.file_len = struct.unpack("!L", buffer)[0]
            print ("File length sent: " + str(self.file_len) + " bytes")
            return self.file_len

        # sets the starting sequence number and creates data packets starting
        # from this number

        start_sequence_no = self.sequence_no
        total_packets = self.create_data_packets(buffer)

        # creates another thread that is responsible for receiving acks for the
        # data packets sent
        recv_ack_thread = threading.Thread(target=self.recv_acks, args=())
        recv_ack_thread.setDaemon(True)
        recv_ack_thread.start()

        packet_to_tx = START_CONG_PACKETS_NUMER

        print "Starts the data transmission. Time needed is dependent on transmitted file size."
        while not self.can_close:
            # calculates the index from which to start sending packets
            # when sending the first time, it will be 0
            # otherwise, when retransmitting, it will calculate the Go-Back-N
            # based
            # on the last data packet that was acked

            if self.last_data_packet_acked is None:
                resend_start_index = 0
            else:
                resend_start_index = int(self.last_data_packet_acked[PACKET_ACK_NO_INDEX]) - start_sequence_no

            # checks if the packet to start retransmitting from is the total
            # amount of packets this
            # would mean the last data packet has been transmitted and so its
            # safe to close the connection
            if resend_start_index >= total_packets:
                self.can_close = True

            # adjusts retransmit to indicate that the sender started
            # retransmitting using locks
            self.retransmit_lock.acquire()
            if self.retransmit == True:
                #print "reset Cong window"
                packet_to_tx = START_CONG_PACKETS_NUMER
            self.retransmit = False
            self.retransmit_lock.release()

             # we start from 2 and then increase exponentially

            # continually tries to transmit packets while the connection cannot
            # be closed from resend start index
            # to the rest of the packets (or at least until as much as it can)
            while not self.can_close and resend_start_index < total_packets and not self.retransmit:
                # tries to send the packet and catches any connection refused
                # exception which might mean
                # the connection was unexpectedly closed/broken

                sent_packets = 0
                #print "Send ", packet_to_tx , "packets"
                while sent_packets < packet_to_tx and resend_start_index < total_packets:
                    if self.get_window_size() > MAXIMUM_PACKET_SIZE:
                        try:
                            self.sendto_encrypted(self.data_packets[resend_start_index], self.send_address)
                            sent_packets += 1
			    #print "#"
                        # Catch error 111 (Connection refused) in the case where the
                        # last ack
                        # was received by this sender and thus the connection was
                        # closed
                        # by the receiver but it happened between this sender's
                        # checking
                        # of that connection close condition
                        except syssock.error, error:
                            if error.errno != 111: #support Wondows error codes as well
                                raise error
                            self.can_close = True
                            break
                        resend_start_index += 1
                    else:
                        print "let's reset congestion window len"
                        packet_to_tx = START_CONG_PACKETS_NUMER
                        time.sleep(0.1)
                time.sleep(0.2)
                #print "looks like no packet drops. let's double number of packets sent at once"
                packet_to_tx *=2
	        packet_to_tx = packet_to_tx % 65
                

        # waits for recv thread to finish before returning from the method
        recv_ack_thread.join()

        print ("Finished transmitting data packets")
        return len(buffer)

    # method responsible for receiving acks for the data packets the sender
    # sends
    def recv_acks(self):
        # tries to receive the ack as long as the connection has is not ready
        # to be closed
        # this can only happen when the sender receives a Connection refused
        # error
        last_ack = time.clock()

        while not self.can_close:
            # tries to receive the new packet and un-pack it
            try:
                current_time = time.clock()
	        #print "Cur time" , current_time, "Last time " , last_ack
                delta_ack = current_time - last_ack

                if delta_ack > 0.02:
                    self.can_close = True
                    continue;

                #print "time delta ack: ", delta_ack
                #print "Current Window ",  self.get_window_size()
                new_packet = self.recv_decrypted()
                new_packet = struct.unpack(PACKET_HEADER_FORMAT, new_packet)

                if new_packet[PACKET_FLAG_INDEX] == SOCK352_FIN:
                    # Received SOCK352_FIN. Closing connection Gracefully
                    self.fin_received = True
                elif new_packet[PACKET_FLAG_INDEX] == SOCK352_RESET:
                    # Received SOCK352_RESET
                    self.can_close = True
                    continue
                #close connection gracefully
                # ignores the packet if the ACK flag is not set.
                elif new_packet[PACKET_FLAG_INDEX] != SOCK352_ACK:
                    # It is bad conditin if we are here. Stop processing
                    self.can_close = True
                    self.reset = True
                    continue
		
		last_ack = time.clock()
                
                self.set_window_size(new_packet[WINDOW_NO_INDEX])
                # print "dow ",  self.get_window_size()
                # if the last data packet acked is not set, the newly received
                # packet is set to be the last data packet
                # acked.  Otherwise, checks if the new packet's sequence number
                # is greater than the last data packet
                # acked's sequence number, otherwise it assumes it could be a
                # duplicate ACK
                self.window_buffer_lock.acquire()
                if self.last_data_packet_acked is None or \
                        new_packet[PACKET_SEQUENCE_NO_INDEX] > self.last_data_packet_acked[PACKET_SEQUENCE_NO_INDEX]:
                    self.last_data_packet_acked = new_packet
                self.window_buffer_lock.release()

            # in the case where the recv times out, it locks down retransmit
            # and sets it to True
            # to indicate that no ACk was received within the timeout window of
            # 0.2 seconds
            except syssock.timeout:
                self.retransmit_lock.acquire()
                self.retransmit = True
                self.retransmit_lock.release()

            # Catch error 111 (Connection refused) in the case where the sender
            # is
            # anticipating an ACK for a packet it sent out, which hasn't timed
            # out
            # but the server has closed the connection since it finished
            # receiving
            # the data and an ACK is already on its way to this sender
            except syssock.error, error:
                if error.errno != 111: 
                    self.can_close = True
                    raise error
                self.can_close = True
                return


    def recv(self, nbytes):
        if self.file_len == - 1:
            file_size_packet = self.recv_decrypted()
            self.file_len = struct.unpack("!L", file_size_packet)[0]
            print ("File Length Received: " + str(self.file_len) + " bytes")
            return file_size_packet

        if self.recv_data_not_started:
            recv_data_thread = threading.Thread(target=self.recv_data, args=())
            recv_data_thread.setDaemon(True)
            recv_data_thread.start()
            self.recv_data_not_started = False

        reseived_data = bytearray(nbytes)
        bytes_received = 0
        while True:
            (out_data, data_len) = self.extract_requested_data(nbytes - bytes_received)
            #print "received: ", data_len
            ack_packet = self.createPacket(flags=SOCK352_ACK,
                                            sequence_no=self.sequence_no,
                                            ack_no=self.ack_no)
            # the sequence number is incremented since it was consumed upon packet
            # creation
            self.sequence_no += 1

            self.sendto_encrypted(ack_packet, self.send_address)
            
            if data_len > 0:
                reseived_data[bytes_received:] = out_data
                bytes_received += data_len
                if bytes_received >= nbytes:
                    print "Received whole file. Exit loop"
                    break 
            # finally, it creates the ACK packet using the server's current
            # sequence and ack numbers


           # time.sleep(0.1)

        return reseived_data
    # method responsible for receiving the data packets (used by the receiver)

    def recv_data(self):
        #we are ging to receive as much as client would like to send to us.
        data_received = ""
        print ("Started receiving data packets...")
        # keep trying to receive packets until the receiver has more bytes left
        # to receive
        #self.socket.settimeout(0.2)
        while True:
            # tries to receive the packet
            try:
                # receives the packet of header + maximum data size bytes
                # (although it will be limited
                # by the sender on the other side)
                packet_received = self.recv_decrypted()

                # sends the packet to another method to manage it and gets back
                # the data in return
                str_received = self.manage_recvd_data_packet(packet_received)

                if(self.can_close == True): # True only if RESET received
                    break

                if(self.closing == True): # True only if RESET received
                    break

                # adjusts the numbers accordingly based on return value of
                # manage data packet
                if str_received is not None:
                    # appends the data received to the total buffer of all the
                    # data received so far
                    data_received += str_received

            # catches timeout, in which case it just tries to get another packet
            except syssock.timeout:
                pass
        # since it's done with receiving all the bytes, it marks the socket as
        # safe to close
        self.can_close = True

        print ("Finished receiving the data")
        # returns the data received
        return data_received

    # creates a generic packet to be sent using parameters that are
    # relevant to Part 1.  The default values are specified above in case one
    # or more parameters are not used
    def createPacket(self, flags=0x0, sequence_no=0x0, ack_no=0x0, payload_len=0x0):
        return struct.Struct(PACKET_HEADER_FORMAT).pack(0x1,  # version
                flags,  # flags
                self.encrypt,  # opt_ptr
                0x0,  # protocol
                PACKET_HEADER_LENGTH,  # header_len
                0x0,  # checksum
                0x0,  # source_port
                0x0,  # dest_port
                sequence_no,  # sequence_no
                ack_no,  # ack_no
                self.get_window_size(),  # window
                payload_len  # payload_len
            )

    # Manages a packet received based on the flag
    def manage_recvd_data_packet(self, packet):
        packet_header = packet[:PACKET_HEADER_LENGTH]
        packet_data = packet[PACKET_HEADER_LENGTH:]
        packet_header = struct.unpack(PACKET_HEADER_FORMAT, packet_header)
        packet_header_flag = packet_header[PACKET_FLAG_INDEX]


        if packet_header[PACKET_FLAG_INDEX] == SOCK352_FIN:
            print "\nReceived SOCK352_FIN. Closing connection Gracefully\n"
            self.fin_received = True               
        elif packet_header[PACKET_FLAG_INDEX] == SOCK352_RESET:
            print "\nReceived SOCK352_RESET\n"
            self.can_close = True
            self.reset = True
            return

        # Check if the packet that was received has the expected sequence no
        # for the next in-order sequence no (which is the ack number)
        #     Case 1, the sequence number is in-order so send back the
        #     acknowledgement
        #     Case 2, the sequence number is out-of-order so drop the packet
        if packet_header[PACKET_SEQUENCE_NO_INDEX] != self.ack_no:
            return

        # adds the payload data to the data packet array
        #self.data_packets.append(packet_data)
        if packet_data.__len__() > 0:
            out_len = self.insert_received_data(packet_data, packet_data.__len__())

            if out_len > 0:
                # increments the acknowledgement by 1 since it is supposed to be the
                # next expected sequence number
                self.ack_no += 1
                # finally, it creates the ACK packet using the server's current
                # sequence and ack numbers
                ack_packet = self.createPacket(flags=SOCK352_ACK,
                                               sequence_no=self.sequence_no,
                                               ack_no=self.ack_no)
                # the sequence number is incremented since it was consumed upon packet
                # creation
                self.sequence_no += 1
                # the server sends the packet to ACK the data packet it received
                self.sendto_encrypted(ack_packet, self.send_address)
            else:
                self.dropped_rx_packets += 1
                print "No room for the data. Drop this packet. Don't send ack. Total: ", self.dropped_rx_packets, "Len: ", packet_data.__len__()

        # the data or the payload is then itself is returned from this method
        return packet_data
    
    def sendto_encrypted(self, data, addr):
        if(self.encrypt == True):
            if len(data) > SECURE_HDR_SIZE:
                header = data[:SECURE_HDR_SIZE]
                encrypted_data = self.socket_box.encrypt(data[SECURE_HDR_SIZE:], self.nonce)
                data = header + encrypted_data
                if(MAXIMUM_PACKET_SIZE < len(encrypted_data)):
                    raise Exception(len(encrypted_data))
        return self.socket.sendto_bad(data, addr)

    def recv_decrypted(self):
        if(self.encrypt == True):
            decrypted_packet = ''
            packet = self.socket.recv(MAXIMUM_PACKET_SIZE)
            if(self.socket_box == None):
                self.socket_box = Box(privateKeys.get(('*', 0)), publicKeys.get(address))
            if len(packet) > SECURE_HDR_SIZE:
                payload = packet[SECURE_HDR_SIZE:]
                decrypted_packet = self.socket_box.decrypt(payload)
            packet = packet[:SECURE_HDR_SIZE] + decrypted_packet
            return packet
        data = self.socket.recv(MAXIMUM_PACKET_SIZE)
        return data

    def recvfrom_decrypted(self):
        if(self.encrypt == True):
            decrypted_packet = ''
            (packet, address) = self.socket.recvfrom(MAXIMUM_PACKET_SIZE)
            if(self.socket_box == None):
                self.socket_box = Box(privateKeys.get(('*', 0)), publicKeys.get(address))
            if len(packet) > SECURE_HDR_SIZE:
                payload = packet[SECURE_HDR_SIZE:]
                decrypted_packet = self.socket_box.decrypt(payload)
                packet = packet[:SECURE_HDR_SIZE] + decrypted_packet
            return (packet, address)
        # If not encrypted ----------------------------------------------
        return self.socket.recvfrom(MAXIMUM_PACKET_SIZE)
        

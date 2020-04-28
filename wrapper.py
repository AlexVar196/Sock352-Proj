import random
import socket as sock
drop = 0 #set to 0 to drop packets and 1 to never drop packets
drop_freq = 2 # 1 out of this many packets dropped
num_for_handshake = 4 #for this many packets we will never drop
class badSocket(sock.socket):
	def __init__(self, *arg):
		self.AF_INET = sock.AF_INET 
		self.SOCK_DGRAM = sock.SOCK_DGRAM
		self.num = num_for_handshake
		super(badSocket,self).__init__(*arg)
	def socket(self, *arg):
		return badSocket(sock.AF_INET, sock.SOCK_DGRAM)
	def sendto_bad(self, data, addr):
		self.num -= 1
		if random.randint(drop,drop_freq) or self.num > 0:
#		if True:
#			print('sending this packet', len(data), "Flag ", data[1])
			return super(badSocket, self).sendto(data, addr)
		else:
			#print('dropping this packet', len(data), "Flag ", data[1])
			return len(data)
	def send_bad(self, data):
		self.num -= 1
		if True: #random.randint(drop,drop_freq) or self.num > 0:
			print('sending this packet')
			return super(badSocket, self).send(data)
		else:
			print('dropping this packet')
			return len(data)
	def sendall_bad(self, data):
		return self.send_bad(data)
def socket(self, *arg):
	return badSocket(sock.AF_INET, sock.SOCK_DGRAM)
AF_INET = sock.AF_INET 
SOCK_DGRAM = sock.SOCK_DGRAM
error = sock.error
timeout = sock.timeout
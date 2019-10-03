import random
import networkx as nx
import numpy as np
import matplotlib.pyplot as plt
from collections import OrderedDict, Callable
import warnings
import collections

warnings.filterwarnings('ignore')

'''
Server Class: Representing the agents or more specifically servers in the Ripple network
'''

class Server:
    def __init__(self, server_id):

        '''
        Server attributes
        1. server_id: Unique id for Server/Agent
        2. e2c_latency: End to Core Latency describing the latency from a Server to a neighbouring Server
        3. unl: List of trusted servers, also known as the Unique Node List
        4. links: List of connected servers   
        5. server_time_stamps: Dictionary of known server time stamps
        6. server_positions: Dictionary of known server positions 
        7. messages_sent: Number of messages sent by the server
        8. messages_received: Number of messages received by the server
        '''

        global num_servers
        self.server_id = server_id
        self.e2c_latency = 0
        self.unl = []
        self.links = []
        self.server_time_stamps = collections.defaultdict(int)
        self.server_positions = collections.defaultdict(int)
        self.messages_sent = 0
        self.messages_received = 0

    def check_unl(self, check_server):

        '''
        Server method check_unl:
        Return True if the server belongs to the UNL of this server else returns False
        '''

        for server in self.unl:
            if check_server == server:
                return True
        return False

    def check_link(self, check_server):

        '''
        Server method check_link:
        Return True is the server is connected or linked to this server else returns Fals
        '''

        for link in self.links:
            if check_server == link.link_to:
                return True
        return False

    def receive_message(self, message, network):

        '''
        Server method receive_message
        The server updates its knowledge of server states concerning the network 
        based on the message received, undergoes state change depending on its 
        position and intent(honest/malicious) and further broadcasts its 
        updated state to the network.
        '''

        global positive_servers, negative_servers

        self.messages_received += 1

        # If the message was being sent to itself, the server ignores the data but updates the outbound message.
        for link in self.links:
            if (link.link_to == message.message_from) and (link.message_send_time >= network.master_time):
                link.message.del_positions(message.server_data)
                break

        # Server updates its existing knowledge of the Server States and Server Time stamps.
        broadcast_changes = collections.defaultdict(ServerState)

        for server_id, server_state in message.server_data.items():
            if (server_id != self.server_id) and (
                self.server_positions[server_id] != server_state.server_position) and (
                        server_state.time_stamp > self.server_time_stamps[server_id]):
                self.server_positions[server_id] = server_state.server_position
                self.server_time_stamps[server_id] = server_state.time_stamp
                broadcast_changes[server_id] = server_state

        # No changes to be broadcasted to the network
        if len(broadcast_changes) == 0:
            return

        # Choose our Position change
        unl_count = 0
        unl_balance = 0

        # Calcuates server votes from the UNL
        for server_id in self.unl:

            if (self.server_positions[server_id] == 1):
                unl_count += 1
                unl_balance += 1

            if (self.server_positions[server_id] == -1):
                unl_count += 1
                unl_balance -= 1

        # Malicious server completely disagrees with the votes
        if self.server_id < malicious_servers:
            unl_balance = -unl_balance

        # Adding a negative bias with time to favour 'no'
        unl_balance -= int(network.master_time / 250)

        pos_change = False

        # Enough data to make choose a position
        if (unl_count >= unl_threshold):

            if (self.server_positions[self.server_id] == -1) and (unl_balance > self_weight):

                # If enough servers in the unl on aggregate vote in favour of 'yes', the server switches from 'no' to 'yes'
                self.server_positions[self.server_id] = 1
                positive_servers += 1
                negative_servers -= 1
                self.server_time_stamps[self.server_id] += 1
                broadcast_changes[self.server_id] = ServerState(self.server_id, self.server_time_stamps[self.server_id],
                                                                self.server_positions[self.server_id])
                pos_change = True

            elif (self.server_positions[self.server_id] == 1) and (unl_balance < (-self_weight)):

                # If enough servers in the unl on aggregate vote in favour of 'no', the server switches from 'yes' to 'no'
                self.server_positions[self.server_id] = -1
                positive_servers -= 1
                negative_servers += 1
                self.server_time_stamps[self.server_id] += 1
                broadcast_changes[self.server_id] = ServerState(self.server_id, self.server_time_stamps[self.server_id],
                                                                self.server_positions[self.server_id])
                pos_change = True

        # Broadcast the message
        for link in self.links:

            if (pos_change) or (link.link_to != message.message_from):

                # Update a message that wasn't sent or broadcasted
                if link.message_send_time > network.master_time:
                    link.message.add_positions(broadcast_changes)

                # Broadcast the changes
                else:
                    send_time = network.master_time

                    # Delay the message to coalesce
                    if not (pos_change):
                        send_time += base_delay

                        # Delay more if a packet is on the wire
                        if link.message_receive_time > send_time:
                            send_time += int(link.total_latency / packets_on_wire)

                    # Construct the message that needs to be sent/broadcasted
                    new_message = Message(self.server_id, link.link_to)
                    new_message.server_data = broadcast_changes

                    # Send/Broadcast the message
                    network.send_message(new_message, link, send_time)
                    self.messages_sent = self.messages_sent + 1


'''
Link Class: Connection or link from one server to another.
'''


class Link:
    def __init__(self, link_to, total_latency):
        '''
        Link attributes
        1. link_to: Server id of the connected server.
        2. total_latency: Total latency is the combined end to core latencies of the two connected servers and 
                          the additional core to core latency as the connected servers might be far away.
        3. message_send_time: Time at which the message is sent across the link. 
        4. message_receive_time: Time at which the message is received across the link, equals the send time plus 
                                 the total latency across the link.
        5. message: Message being sent across the link.
        '''

        self.link_to = link_to
        self.total_latency = total_latency
        self.message_send_time = 0
        self.message_receive_time = 0
        self.message = None


'''
Network Class: Message Transfer and Events Update
'''


class Network:
    def __init__(self):
        '''
        Network attributes
        1. master_time: Indicates the time at which the simulation is currently running. 
        2. events: Dictionary of events that need to be executed as the time or master_time progresses
        '''

        self.master_time = 0
        self.events = collections.defaultdict(Event)

    def send_message(self, message, link, send_time):
        '''
        Network method send_message:
        The network sends the message through the link by updating the sending and receiving times of the message
        along with the message being sent across the link. It also updates its events dictionary as it receives 
        multiple messages at a given time.
        '''

        link.message_send_time = send_time
        link.message_receive_time = send_time + link.total_latency
        # The message is appended to the event dictionary along with the expected receive time.
        self.events[link.message_receive_time].add_message(message)
        link.message = self.events[link.message_receive_time].return_message()


'''
Event Class: An event or collection of messages
'''


class Event:
    def __init__(self):
        '''
        Event attributes
        1. messages: List of messages that need to be sent at a particular instance
        '''

        self.messages = []

    def add_message(self, message):
        '''
        Event method add_message
        This method appends a message to its list of messages that are associated with a 
        particular time in the simulation.
        '''

        self.messages.append(message)

    def return_message(self):
        '''
        Event method return_message
        This method returns the most recenly added message from its list of messages. 
        '''

        return list(reversed(self.messages))[0]


'''
Message Class: Representing a message that needs to be sent from one server to another 
                regarding its position. 
'''


class Message:
    def __init__(self, message_from, message_to):

        '''
        Message attributes
        1. message_from: Server id of the server that sends to message. 
        2. message_to: Server id of the server that receives the message. 
        3. server_data: Dictionary of all server posititions known to the sending server.
        '''

        self.message_from = message_from
        self.message_to = message_to
        self.server_data = collections.defaultdict(ServerState)

    def add_positions(self, updated_server_data):

        '''
        Message method add_positions
        This method either updates the existing server positions known to the server or adds 
        the newly transmitted server position
        '''

        server_data_keys = []
        for server_key, server_value in self.server_data.items():
            server_data_keys.append(server_key)

        for server_id, updated_state in updated_server_data.items():

            if server_id != self.message_to:

                if server_id in server_data_keys:

                    if updated_state.time_stamp > self.server_data[server_id].time_stamp:
                        self.server_data[server_id].time_stamp = updated_state.time_stamp
                        self.server_data[server_id].server_position = updated_state.server_position

                else:
                    self.server_data[server_id] = updated_state

    def del_positions(self, received_server_data):

        '''
        Message method del_positions
        This method deletes the data from the message that was sent to itself.
        '''

        server_data_keys = []
        for server_key, server_value in self.server_data.items():
            server_data_keys.append(server_key)

        for server_id, server_state in received_server_data.items():

            if server_id != self.message_to:

                if server_id in server_data_keys:

                    if server_state.time_stamp >= self.server_data[server_id].time_stamp:
                        # Data not needed by the server itself
                        del self.server_data[server_id]


'''
ServerState Class: Representing a server's state or position  with respect to the consensus (agree or disagree). 
'''


class ServerState:
    '''
    ServerState attributes
    1. server_id: Server id of the server.
    2. time_stamp: Time stamp of the server as we proceed with the consensus process. 
    3. server_position: State of the server which could either be a 1 if the server agrees 
                     with the transaction or -1 if it disagrees with the transaction.
    '''

    def __init__(self, server_id, time_stamp, server_position):
        self.server_id = server_id
        self.time_stamp = time_stamp
        self.server_position = server_position


'''
DefaultOrderedDict Class: Converts an OrderedDict to a default OrderedDict so that so dynamic 
                          key-value pairs could be added to the dictionary
'''


class DefaultOrderedDict(OrderedDict):
    '''
    Source: http://stackoverflow.com/a/6190500/562769 
    '''

    def __init__(self, default_factory=None, *a, **kw):
        if (default_factory is not None and
                not isinstance(default_factory, Callable)):
            raise TypeError('first argument must be callable')
        OrderedDict.__init__(self, *a, **kw)
        self.default_factory = default_factory

    def __getitem__(self, key):
        try:
            return OrderedDict.__getitem__(self, key)
        except KeyError:
            return self.__missing__(key)

    def __missing__(self, key):
        if self.default_factory is None:
            raise KeyError(key)
        self[key] = value = self.default_factory()
        return value

    def __reduce__(self):
        if self.default_factory is None:
            args = tuple()
        else:
            args = self.default_factory,
        return type(self), args, None, None, self.items()

    def copy(self):
        return self.__copy__()

    def __copy__(self):
        return type(self)(self.default_factory, self)

    def __deepcopy__(self, memo):
        import copy
        return type(self)(self.default_factory,
                          copy.deepcopy(self.items()))

    def __repr__(self):
        return 'OrderedDefaultDict(%s, %s)' % (self.default_factory,
                                               OrderedDict.__repr__(self))

def UNL_Overlap_test_One(num_servers,servers_list):

    print('--------------------------------------------------------------\n')
    print('CHECKING UNL OVERLAP CONDITION (TEST 1)')
    print('--------------------------------------------------------------')

    for i in range(num_servers):
        unl_1 = servers_list[i].unl
        unl_1_size = len(unl_1)

        for j in range(num_servers):

            if i!=j:
                unl_2 = servers_list[j].unl
                unl_2_size = len(unl_2)
                unl_overlap = len(list(set(unl_1).intersection(unl_2)))
                if(unl_1_size>unl_2_size):
                    if (unl_overlap>= 0.2*unl_1_size):
                        pass
                    else:
                        print('\nPossibility of fork: ' + 'Insufficient UNL overlap between servers ' + str(i) + ' and ' + str(j))
                        print('\nUNL of server ' + str(i) + ' : ' + str(unl_1))
                        print('\nUNL of server ' + str(j) + ' : ' + str(unl_2))
                        print('\nUNL overlap ' + str(list(set(unl_1).intersection(unl_2))))
                        return

                else:
                    if (unl_overlap>= 0.2*unl_2_size):
                        pass
                    else:
                        print('\nPossibility of fork: ' + 'Insufficient UNL overlap between servers ' + str(i) + ' and ' + str(j))
                        print('\nUNL of server ' + str(i) + ' : ' + str(unl_1))
                        print('\nUNL of server ' + str(j) + ' : ' + str(unl_2))
                        print('\nUNL overlap ' + str(list(set(unl_1).intersection(unl_2))))
                        return

    return


def UNL_Overlap_test_Two(num_servers,servers_list):

    print('--------------------------------------------------------------\n')
    print('CHECKING UNL OVERLAP CONDITION (TEST 2)')
    print('--------------------------------------------------------------')
    for i in range(num_servers):
        unl_1 = servers_list[i].unl
        unl_1_size = len(unl_1)
        for j in range(unl_1_size):
            server_id = unl_1[j]
            print(server_id)
            unl_2 = servers_list[server_id].unl
            unl_2_size = len(unl_2)
            unl_overlap = len(list(set(unl_1).intersection(unl_2)))
            if (unl_1_size > unl_2_size):
                if (unl_overlap >= 0.2 * unl_1_size):
                    pass
                else:
                    print('\nPossibility of fork: ' + 'Insufficient UNL overlap between servers ' + str(
                        i) + ' and ' + str(server_id))
                    print('\nUNL of server ' + str(i) + ' : ' + str(unl_1))
                    print('\nUNL of server ' + str(server_id) + ' : ' + str(unl_2))
                    print('\nUNL overlap ' + str(list(set(unl_1).intersection(unl_2))))
                    return
            else:
                if (unl_overlap >= 0.2 * unl_2_size):
                    pass
                else:
                    print('\nPossibility of fork: ' + 'Insufficient UNL overlap between servers ' + str(
                        i) + ' and ' + str(server_id))
                    print('\nUNL of server ' + str(i) + ' : ' + str(unl_1))
                    print('\nUNL of server ' + str(server_id) + ' : ' + str(unl_2))
                    print('\nUNL overlap ' + str(list(set(unl_1).intersection(unl_2))))
                    return

    return



'''
main() function initializes the network and runs the Ripple simulation until consensus is reached.
'''


def main():
    # Declaring all the global variables used in other classes and methods
    global positive_servers, negative_servers, num_servers, malicious_servers, unl_threshold, self_weight, base_delay, packets_on_wire, consensus_percent

    # Initalizing the global and local variables (Values taken from the Ripple sim code on Github)
    positive_servers = 0
    negative_servers = 0

    num_servers = 100
    malicious_servers = 15

    server_outbound_links = 10
    unl_min = 20
    unl_max = 30
    unl_threshold = int(unl_min / 2)

    min_e2c_latency = 5
    max_e2c_latency = 50
    min_c2c_latency = 5
    max_c2c_latency = 200

    self_weight = 1
    base_delay = 1
    packets_on_wire = 3
    consensus_percent = 80
    seed_counter = 0

    G = nx.Graph()

    print('INPUT VALUES\n')
    print('1) Network Size : ' + str(num_servers))
    print('2) Malicious Servers : ' + str(malicious_servers))
    print('3) Outbound Links : ' + str(server_outbound_links))
    print('4) (Min UNL size, Max UNL size, UNL threshold) : (' + str(unl_min) + ', ' + str(unl_max) + ', ' + str(
        unl_threshold) + ')')
    print('5) (Min e2c latency, Max e2c latency) : (' + str(min_e2c_latency) + ', ' + str(max_e2c_latency) + ')')
    print('6) (Min c2c latency, Max c2c latency) : (' + str(min_c2c_latency) + ', ' + str(max_c2c_latency) + ')')

    # Initializing a list of all servers in the network
    servers_list = []
    for i in range(num_servers):
        new_server = Server(i)
        servers_list.append(new_server)

    print('\nRUNNING SIMULATION\n')

    # Initializing server attributes: latency, server states, server time stamp and unl
    print('1) Initialing Servers')

    for i in range(num_servers):

        # Comment the random seed function to generate different end to core latency values on each run
        np.random.seed(i)
        servers_list[i].e2c_latency = round(np.random.uniform(min_e2c_latency, max_e2c_latency))

        for j in range(num_servers):
            if i == j:
                if (i % 2):
                    servers_list[i].server_positions[i] = 1
                    servers_list[i].server_time_stamps[i] = 1
                    positive_servers += 1
                else:
                    servers_list[i].server_positions[i] = -1
                    servers_list[i].server_time_stamps[i] = 1
                    negative_servers += 1
            else:
                servers_list[i].server_positions[j] = 0
                servers_list[i].server_time_stamps[j] = 0

        # Comment the random seed function to generate different UNL sizes on each run
        np.random.seed(i)
        unl_count = round(np.random.uniform(unl_min, unl_max))

        while unl_count > 0:

            # Comment the random seed function to generate different UNL servers on each run
            np.random.seed(i + seed_counter)
            unl_server = round(np.random.uniform(0, num_servers - 1))

            if unl_server != i and not servers_list[i].check_unl(unl_server):
                servers_list[i].unl.append(unl_server)
                unl_count -= 1
            seed_counter += 1

    #print(servers_list[0].unl)
    #print(servers_list[1].unl)
    #print(list(set(servers_list[0].unl).intersection(servers_list[1].unl)))
    #print(0.2*len(servers_list[0].unl))

    # Assigning unique random colors to all servers for clear visualization
    L = [i for i in range(num_servers)]
    colors_list = []
    for i in range(num_servers):
        successful = False
        while not successful:

            # Comment the random seed function to generate different random colors on each run
            random.seed(i + seed_counter)
            rand_color = (random.random(), random.random(), random.random(), random.random())

            if rand_color not in colors_list:
                colors_list.append(rand_color)
                break
            else:
                successful = True
                seed_counter += 1

    G.add_nodes_from(L)

    # Initializing Links to all servers in the graph above
    print('2) Initialing Links')
    for i in range(num_servers):

        num_links = server_outbound_links

        while num_links > 0:

            # Comment the random seed function to generate different server links on each run
            np.random.seed(i + num_servers + seed_counter)
            link_server = round(np.random.uniform(0, num_servers - 1))

            if link_server != i and not servers_list[i].check_link(link_server) and not servers_list[
                link_server].check_link(i):
                # Comment the random seed function to generate different core to core latency on each run
                np.random.seed(i + num_servers + seed_counter)
                c2c_latency = round(np.random.uniform(min_c2c_latency, max_c2c_latency))

                tot_latency = servers_list[i].e2c_latency + servers_list[link_server].e2c_latency + c2c_latency
                servers_list[i].links.append(Link(link_server, tot_latency))
                servers_list[link_server].links.append(Link(i, tot_latency))
                num_links -= 1
            seed_counter += 1

    # Adding the links generated
    for i in range(num_servers):
        for j in range(len(servers_list[i].links)):
            G.add_edges_from([(i, servers_list[i].links[j].link_to)])

    network = Network()

    print('3) Network Created \n')


    UNL_Overlap_test_One(num_servers,servers_list)
    UNL_Overlap_test_One(num_servers, servers_list)

    return


    # Broacasting initial positions to the connected servers
    print('3) Broadcasting initial messages')

    for i in range(num_servers):
        link_num = 0
        for link in servers_list[i].links:
            m = Message(i, link.link_to)
            m.server_data[i] = ServerState(i, 1, servers_list[i].server_positions[i])
            network.send_message(m, link, 0)
            link_num += 1

    messages_created = 0
    for event_time, event in network.events.items():
        messages_created += len(event.messages)
        # print(str(len(value.messages)) + ' Event Messages created\n')

    print('4) ' + str(len(network.events)) + ' Events created and ' + str(messages_created) + ' Messages created')
    print('5) Running Ripple Consensus protocol (might take some time) \n')

    # Starts the consensus process until a final decision is reached
    while True:

        # Majority servers agree with the transactions
        if positive_servers > (num_servers * (consensus_percent / 100)):
            print('\nPERFORMANCE MEASURES\n')
            print('1) Consensus outcome: Majority of Servers agree on the transaction')
            print('2) Positive servers: ' + str(positive_servers))
            print('3) Negative servers: ' + str(negative_servers))
            break

        # Majority servers disagree with the transactions
        if negative_servers > (num_servers * (consensus_percent / 100)):
            print('\nPERFORMANCE MEASURES\n')
            print('1) Consensus outcome: Majority of servers disagree on the transaction')
            print('2) Positive servers: ' + str(positive_servers))
            print('3) Negative servers: ' + str(negative_servers))
            break

        ordered_network_events = collections.OrderedDict(sorted(network.events.items()))
        network.events = DefaultOrderedDict(Event)

        for event_time, event in ordered_network_events.items():
            network.events[event_time] = event

        # Events are sequantially iterated
        event_iter = iter(network.events)

        try:
            event_time = event_iter.__next__()
            event = network.events[event_time]

        except StopIteration:
            print('\nPERFORMANCE MEASURES\n')
            print('1) Consensus outcome: No messages to send. Aborting Consensus.')
            print('2) Positive servers: ' + str(positive_servers))
            print('3) Negative servers: ' + str(negative_servers))
            break

        if int(event_time / 100) > int(network.master_time / 100):
            print('Time : ' + str(event_time) + ' ms ' + ' Servers+/Servers- : ' + str(positive_servers) + '/' + str(
                negative_servers))

        network.master_time = event_time

        # Transmission of messages
        for m in event.messages:
            if len(m.server_data) == 0:
                servers_list[m.message_from].messages_sent -= 1
            else:
                servers_list[m.message_to].receive_message(m, network)

        del network.events[event_time]

    message_count = 0
    for event_time, event in network.events.items():
        message_count += len(event.messages)

    # Final Consensus results are captured
    print('4) Consensus time : Consensus reached in ' + str(network.master_time) + ' ms with ' + str(
        message_count) + ' messages on the wire.')

    total_messages_sent = 0

    for i in range(num_servers):
        total_messages_sent += servers_list[i].messages_sent

    print('5) Message rate : An average server sent ' + str(total_messages_sent / num_servers) + ' messages.\n')


if __name__ == "__main__":
    main()
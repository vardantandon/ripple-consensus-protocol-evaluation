import networkx as nx
import numpy as np
from collections import OrderedDict, Callable
import warnings
import multiprocessing
import collections
import itertools

warnings.filterwarnings('ignore')

'''
Server Class: An Agent or server in the Ripple network
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
                link.message.del_states(message.server_data)
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
                    link.message.update_states(broadcast_changes)

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
Message Class: Representing a message that needs to be sent.           
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

    def update_states(self, updated_server_data):

        '''
        Message method update_states
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

    def del_states(self, received_server_data):

        '''
        Message method del_states
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
ServerState Class: Representing a server's state with respect to the consensus.  
'''

class ServerState:

    def __init__(self, server_id, time_stamp, server_position):

        '''
        ServerState attributes
        1. server_id: Server id of the server.
        2. time_stamp: Time stamp of the server as we proceed with the consensus process. 
        3. server_position: State of the server which could either be a 1 if the server agrees 
                            with the transaction or -1 if it disagrees with the transaction.
        '''

        self.server_id = server_id
        self.time_stamp = time_stamp
        self.server_position = server_position


'''
DefaultOrderedDict Class: Converts an OrderedDict to a default OrderedDict 
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

'''
main() function receives the input values of the building blocks which are used to construct the network and 
then run the simulation of the Ripple consensus protocol on those set of values 
'''

def main(input_values):

    global positive_servers, negative_servers, num_servers, malicious_servers, unl_threshold, self_weight, base_delay, packets_on_wire, consensus_percent
    positive_servers = 0
    negative_servers = 0

    # The building blocks are initialized with the input values passed for this simulation
    num_servers, malicious_servers, server_outbound_links, unl_range, e2c_latency_range, c2c_latency_range = input_values

    unl_min, unl_max = unl_range
    unl_threshold = int(unl_min / 2)

    min_e2c_latency, max_e2c_latency = e2c_latency_range
    min_c2c_latency, max_c2c_latency = c2c_latency_range

    self_weight = 1
    base_delay = 1
    packets_on_wire = 3
    consensus_percent = 80
    seed_counter = 0
    simulation_summary = []

    G = nx.Graph()

    # Initializing a list of all servers in the network
    servers_list = []
    for i in range(num_servers):
        new_server = Server(i)
        servers_list.append(new_server)

    # Initializing server attributes: latency, server positions, server time stamp and unl
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

    L = [i for i in range(num_servers)]
    G.add_nodes_from(L)

    # Initializing Links to all servers in the graph above
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

    # Broacasting initial positions to the connected servers

    for i in range(num_servers):
        link_num = 0
        for link in servers_list[i].links:
            m = Message(i, link.link_to)
            m.server_data[i] = ServerState(i, 1, servers_list[i].server_positions[i])
            network.send_message(m, link, 0)
            link_num += 1

    num_events = len(network.events)
    messages_created = 0
    for event_time, event in network.events.items():
        messages_created += len(event.messages)

    simulation_summary.extend([num_events, messages_created])
    consensus_summary = []

    # Starts the consensus process until a final decision is reached
    while True:

        # Majority servers agree with the transactions
        if positive_servers > (num_servers * (consensus_percent / 100)):
            simulation_summary.append(1)
            simulation_summary.append(positive_servers)
            simulation_summary.append(negative_servers)
            break

        # Majority servers disagree with the transactions
        if negative_servers > (num_servers * (consensus_percent / 100)):
            simulation_summary.append(-1)
            simulation_summary.append(positive_servers)
            simulation_summary.append(negative_servers)
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
            simulation_summary.append(0)
            simulation_summary.append(positive_servers)
            simulation_summary.append(negative_servers)
            break

        if int(event_time / 100) > int(network.master_time / 100):
            iteration_summary = [event_time, positive_servers, negative_servers]
            consensus_summary.append(iteration_summary)

        network.master_time = event_time

        # Transmission of messages
        for m in event.messages:
            if len(m.server_data) == 0:
                servers_list[m.message_from].messages_sent -= 1
            else:
                servers_list[m.message_to].receive_message(m, network)

        del network.events[event_time]

    simulation_summary.append(consensus_summary)

    message_count = 0
    for event_time, event in network.events.items():
        message_count += len(event.messages)

    # Final Consensus results are captured
    simulation_summary.extend([network.master_time, message_count])

    total_messages_sent = 0

    for i in range(num_servers):
        total_messages_sent += servers_list[i].messages_sent

    message_rate = int(total_messages_sent / num_servers)
    simulation_summary.append(message_rate)

    print('Ran a simulation with ' + str(malicious_servers) + ' malicious servers.')
    return simulation_summary

if __name__ == "__main__":

    # Varying Number of malicious servers while keeping other parameters fixed
    num_nodes_list = list(range(100,200,100))#100
    mal_node_list = list(range(5,35,5)) #5,10..30
    nodes_conn_list = list(range(10, 15, 5)) # 10
    unl_min = list(range(5, 10, 5)) # 5
    unl_max = list(range(15, 20, 5)) # 15
    unl_list = list(zip(unl_min, unl_max)) #(5,15)
    min_e2c_latency = list(range(5, 10, 5)) #5
    max_e2c_latency = list(range(50, 55, 5)) #50
    e2c_latecy_list = list(zip(min_e2c_latency, max_e2c_latency)) #(5,50)
    min_c2c_latency = list(range(5, 10, 5)) #5
    max_c2c_latency = list(range(200, 205, 5)) #200
    c2c_latecy_list = list(zip(min_c2c_latency, max_c2c_latency)) #(5,200)

    param_list = [num_nodes_list, mal_node_list, nodes_conn_list, unl_list, e2c_latecy_list, c2c_latecy_list]

    # Prepares a list of input values as inputs to the simulations
    input_list = list(itertools.product(*param_list))

    print('\nTotal number of Simulations: ' + str(len(input_list)))
    print('------------------------------------------------------------------------\n')

    print('\nProcessing all Simulations via multithreading(This might take a while)')
    print('------------------------------------------------------------------------\n')

    # Pool object that maps the input values and to produce the corresponding results
    pool = multiprocessing.Pool()
    results = pool.map(main, input_list)

    # The results obtains from all simulations are now presented
    for i in range(len(input_list)):

        print('\nSimulation ' + str(i+1) + ' : ')
        print('------------------------------------------------------------------------\n')
        print('INPUT VALUES\n')
        print('1) Network Size : ' + str(input_list[i][0]))
        print('2) Malicious Servers : ' + str(input_list[i][1]))
        print('3) Outbound Links : ' + str(input_list[i][2]))
        print('4) (Min UNL size, Max UNL size) : ' + str(input_list[i][3]))
        print('5) (Min e2c latency, Max e2c latency) : ' + str(input_list[i][4]))
        print('6) (Min c2c latency, Max c2c latency) : ' + str(input_list[i][5]))
        print('\nRUNNING SIMULATION\n')
        print('1) Initialing Servers')
        print('2) Initialing Links')
        print('3) Broadcasting initial messages')
        print('4) ' + str(results[i][0]) + ' Events created and ' + str(results[i][1]) + ' Messages created')
        print('5) Running Ripple Consensus protocol \n')

        for j in range(len(results[i][5])):
            print('Time : ' + str(results[i][5][j][0]) + ' ms ' + ' Servers+/Servers- : ' + str(
                results[i][5][j][1]) + '/' + str(results[i][5][j][2]))

        print('\nPERFORMANCE MEASURES\n')

        if results[i][2] == 1:
            print('1) Consensus outcome: Majority of Servers agree on the transaction')
            print('2) Positive servers: ' + str(results[i][3]))
            print('3) Negative servers: ' + str(results[i][4]))

        elif results[i][2] == -1:
            print('1) Consensus outcome: Majority of servers disagree on the transaction')
            print('2) Positive servers: ' + str(results[i][3]))
            print('3) Negative servers: ' + str(results[i][4]))

        else:
            print('1) Consensus outcome: No messages to send. Aborting Consensus.')
            print('2) Positive servers: ' + str(results[i][3]))
            print('3) Negative servers: ' + str(results[i][4]))

        print('4) Consensus time : Consensus reached in ' + str(results[i][6]) + ' ms with ' + str(
            results[i][7]) + ' messages on the wire.')
        print('5) Message rate : An average server sent ' + str(results[i][8]) + ' messages.\n')
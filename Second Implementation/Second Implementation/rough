import random
import matplotlib.pyplot as plt
from random import randint
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


"""
generate_rand_values(n,min_size,max_size): 
function returns a list of random clique sizes from a range 
of minimum and maximum clique size such that it sums up to 
the total number of servers
"""


def generate_rand_values(n, min_size, max_size):
    values = []
    while n != 0:
        np.random.seed(n)
        value = randint(min_size, max_size)
        values.append(value)
        n -= value
        if n == 0:
            break
        if n < min_size:
            del values[-1]
            n += value
    return values


"""
generate_normal_values(n,mean_size, sd_size, min_size, max_size):
function returns a list of random clique sizes generated using a 
normal distribution from a range of minimum and maximum clique size 
such that it sums up to the total number of servers
"""


def generate_normal_values(n, mean_size, sd_size, min_size, max_size):
    values = []
    while n != 0:
        value = int(np.random.normal(mean_size, sd_size))
        if value < min_size or value > max_size:
            continue
        values.append(value)
        n -= value
        if n == 0:
            break
        if n < min_size:
            del values[-1]
            n += value
    return values


"""
generate_lognormal_values(n,mean_size, sd_size, min_size, max_size): 
function returns a list of random clique sizes generated using a lognormal 
distribution from a range of minimum and maximum clique size 
such that it sums up to the total number of servers
"""


def generate_lognormal_values(n, mean_size, sd_size, min_size, max_size):
    values = []
    while n != 0:
        value = int(np.random.lognormal(mean_size, sd_size))
        if value < min_size or value > max_size:
            continue
        values.append(value)
        n -= value
        if n == 0:
            break
        if n < min_size:
            del values[-1]
            n += value
    return values


"""
generate_rand_values(n, min_overlap, max_overlap):
function returns a list of random overlaps from a range of minimum and maximum overlap
such that it sums up to the total number of combinations for all
cliques.
"""


def generate_rand_overlaps(n, min_overlap, max_overlap):
    values = []
    for i in range(n):
        np.random.seed(i)
        value = randint(min_overlap, max_overlap)
        values.append(value)
    return values


"""
generate_normal_overlaps(n, mean_overlap, sd_overlap, min_size, max_size): 
function returns a list of random overlaps generated using normal distribution 
from a range of minimum and maximum overlap such that it sums up to the 
total number of combinations for all cliques.
"""


def generate_normal_overlaps(n, mean_overlap, sd_overlap, min_size, max_size):
    values = []
    decrement = n
    while decrement != 0:
        value = int(np.random.normal(mean_overlap, sd_overlap))
        if value < min_size or value > max_size:
            continue
        decrement = decrement - 1
        values.append(value)
    return values


"""
generate_rand_values(n,min_size,max_size) function returns a list of 
random overlaps from a range of minimum and maximum overlap
such that it sums up to the total number of combinations for all
cliques.
"""


def generate_lognormal_overlaps(n, mean_overlap, sd_overlap, min_size, max_size):
    values = []
    decrement = n
    while decrement != 0:
        value = int(np.random.lognormal(mean_overlap, sd_overlap))
        if value < min_size or value > max_size:
            continue
        decrement = decrement - 1
        values.append(value)
    return values

def UNL_Overlap_test_One(clique_list):
    print('--------------------------------------------------------------\n')
    print('CHECKING UNL OVERLAP CONDITION (TEST 1)')
    print('--------------------------------------------------------------')

    for i in range(len(clique_list)):
        unl_1 = clique_list[i]
        unl_1_size = len(unl_1)

        for j in range(len(clique_list)):

            if i != j:
                unl_2 = clique_list[j]
                unl_2_size = len(unl_2)



                unl_overlap = len(list(set(unl_1).intersection(unl_2)))
                if (unl_1_size > unl_2_size):
                    if (unl_overlap >= 0.2 * unl_1_size):
                        pass
                    else:
                        print('\nPossibility of fork: ' + 'Insufficient overlap between cliques' + str(
                            i) + ' and ' + str(j))
                        print('\nUNL of server ' + str(i) + ' : ' + str(unl_1))
                        print('\nUNL of server ' + str(j) + ' : ' + str(unl_2))
                        print('\nUNL overlap ' + str(list(set(unl_1).intersection(unl_2))))
                        return

                else:
                    if (unl_overlap >= 0.2 * unl_2_size):
                        pass
                    else:
                        print('\nPossibility of fork: ' + 'Insufficient cliques between cliques ' + str(
                            i) + ' and ' + str(j))
                        print('\nUNL of server ' + str(i) + ' : ' + str(unl_1))
                        print('\nUNL of server ' + str(j) + ' : ' + str(unl_2))
                        print('\nUNL overlap ' + str(list(set(unl_1).intersection(unl_2))))
                        return
    print('Test Passed')
    return

"""
function clique_topology(network_size, clique_seq, overlap_seq, col_list):
returns the Ripple network in the form of an interconnected network of cliques
satisfying atleast a 20% overlap between all UNL pairs.
"""


def clique_topology(network_size, clique_seq, overlap_seq, col_list):
    num_cliques = len(clique_seq)
    L = [i for i in range(0, network_size)]
    G = nx.Graph()
    clique_list = []
    color_included = []
    from_node = []
    to_node = [0]
    seed = 0

    for i in range(0, num_cliques):

        clique_size = clique_seq[i]
        np.random.seed(i + seed)
        clique_color = random.choice(col_list)
        while clique_color in color_included:
            seed += 1
            np.random.seed(i + seed)
            clique_color = random.choice(col_list)
            seed += 1

        color_included.append(clique_color)

        from_node.append(to_node[i])
        to_node.append(to_node[i] + clique_size)

        for j in range(from_node[i], to_node[i + 1]):
            G.add_node(L[j], clique_group=i, color=clique_color)

        edges = itertools.combinations(L[from_node[i]:to_node[i + 1]], 2)
        G.add_edges_from(edges)
        clique_list.append(L[from_node[i]:to_node[i + 1]])

    clique_edges = [x for x in itertools.combinations(clique_list, 2)]

    for i in range(0, len(clique_edges)):
        edges_included = []
        for j in range(0, overlap_seq[i]):
            successful = False
            while not successful:
                edges = (random.choice(clique_edges[i][0]), random.choice(clique_edges[i][1]))
                counter = 0
                for edge in edges_included:
                    if edges[0] in edge:
                        counter = 1
                    if edges[1] in edge:
                        counter = 1
                        break
                if edges not in edges_included and not counter:
                    G.add_edges_from([edges])
                    edges_included.append(edges)
                    successful = True
                else:
                    successful = False


    return G


'''
main() function receives the input values of the building blocks which are used to construct the network and 
then run the simulation of the Ripple consensus protocol on those set of values 
'''


def main(input_values):
    global positive_servers, negative_servers, num_servers, malicious_servers, unl_threshold, self_weight, base_delay, packets_on_wire, consensus_percent

    # Initalizing the global and local variables (Values taken from the Ripple sim code on Github)
    positive_servers = 0
    negative_servers = 0

    # The building blocks are initialized with the input values passed for this simulation
    num_servers, malicious_servers, network_topology, clique_range, e2c_latency_range, c2c_latency_range = input_values

    min_clique_size, max_clique_size = clique_range

    min_e2c_latency, max_e2c_latency = e2c_latency_range
    min_c2c_latency, max_c2c_latency = c2c_latency_range

    min_overlap = min_clique_size / 2
    max_overlap = min_clique_size

    color_list = []
    unl_sizes = []
    seed_counter = 0

    self_weight = 1
    base_delay = 1
    packets_on_wire = 3
    consensus_percent = 80
    simulation_summary = []

    for i in range(num_servers):
        successful = False
        while not successful:

            random.seed(i + seed_counter)
            rand_color = (random.random(), random.random(), random.random(), random.random())

            if rand_color not in color_list:
                color_list.append(rand_color)
                break
            else:
                successful = True
                seed_counter += 1

    mean_clique_size = (min_clique_size + max_clique_size) / 2
    sd_clique_size = mean_clique_size - min_clique_size

    mean_overlap = (min_overlap + max_overlap) / 2
    sd_overlap = mean_overlap - min_overlap

    clique_list_1 = generate_rand_values(num_servers, min_clique_size, max_clique_size)
    clique_list_2 = generate_normal_values(num_servers, mean_clique_size, sd_clique_size, min_clique_size,
                                           max_clique_size)
    clique_list_3 = generate_lognormal_values(num_servers, mean_clique_size, sd_clique_size, min_clique_size,
                                              max_clique_size)

    overlap_num_1 = len([x for x in itertools.combinations(clique_list_1, 2)])
    overlap_num_2 = len([x for x in itertools.combinations(clique_list_2, 2)])
    overlap_num_3 = len([x for x in itertools.combinations(clique_list_3, 2)])

    overlap_list_1 = generate_rand_overlaps(overlap_num_1, min_overlap, max_overlap)
    overlap_list_2 = generate_normal_overlaps(overlap_num_2, mean_overlap, sd_overlap, min_overlap, max_overlap)
    overlap_list_3 = generate_lognormal_overlaps(overlap_num_3, mean_overlap, sd_overlap, min_overlap, max_overlap)

    ### initialize Ripple network
    if network_topology == 1:
        Ripple_net = clique_topology(num_servers, clique_list_1, overlap_list_1, color_list)
    elif network_topology == 2:
        Ripple_net = clique_topology(num_servers, clique_list_2, overlap_list_2, color_list)
    elif network_topology == 3:
        Ripple_net = clique_topology(num_servers, clique_list_3, overlap_list_3, color_list)



    # nx.draw(Ripple_net, node_color=[Ripple_net.node[node]['color'] for node in Ripple_net])
    # plt.show(Ripple_net)

    # Initializing server attributes: latency, server positions, server time stamp and unl
    servers_list = []
    for i in range(num_servers):
        new_server = Server(i)
        servers_list.append(new_server)

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

        servers_list[i].unl = Ripple_net.neighbors(i)
        unl_sizes.append(len(servers_list[i].unl))
        links = Ripple_net.neighbors(i)

        for k in range(len(Ripple_net.neighbors(i))):
            link_server = links[k]
            np.random.seed(k)
            c2c_latency = round(np.random.uniform(min_c2c_latency, max_c2c_latency))
            tot_latency = servers_list[i].e2c_latency + servers_list[link_server].e2c_latency + c2c_latency
            servers_list[i].links.append(Link(link_server, tot_latency))
            servers_list[link_server].links.append(Link(i, tot_latency))

    unl_threshold = min(unl_sizes)

    network = Network()

    UNL_Overlap_test_One(num_servers, servers_list)
    UNL_Overlap_test_One(num_servers, servers_list)

    return

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

        if int(event_time / 20) > int(network.master_time / 20):
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

    # all other prints statements are removed
    print('Ran a simulation for ' + str(num_servers) + ' servers.')

    return simulation_summary


if __name__ == "__main__":

    num_nodes_list = [100]
    mal_node_list = [15]
    network_topology_list = [1]
    clique_list_range = [(4, 6)]
    e2c_latecy_list = [(5, 50)]
    c2c_latecy_list = [(5, 200)]

    param_list = [num_nodes_list, mal_node_list, network_topology_list, clique_list_range, e2c_latecy_list,
                  c2c_latecy_list]

    # Prepares a list of input values with all possible combination of inputs
    input_list = list(itertools.product(*param_list))

    print('\nTotal number of Simulations: ' + str(len(input_list)))
    print('------------------------------------------------------------------------\n')

    print('\nProcessing all Simulations via multithreading(This might take a few minutes)')
    print('------------------------------------------------------------------------\n')

    # Pool object that maps the input values and to produce the corresponding results
    pool = multiprocessing.Pool()
    results = pool.map(main, input_list)

    print('\nSimulation Summary')
    print('------------------------------------------------------------------------\n')

    # The results obtains from all simulations are now presented
    for i in range(len(input_list)):

        print('\nSimulation ' + str(i + 1) + ' : ')
        print('------------------------------------------------------------------------\n')
        print('INPUT VALUES\n')
        print('1) Network Size : ' + str(input_list[i][0]))
        print('2) Malicious Servers : ' + str(input_list[i][1]))
        print('3) Network Topology (1: Random 2: Normal 3: Lognormal) : ' + str(input_list[i][2]))
        print('4) (Min clique size, Max clique size) : ' + str(input_list[i][3]))
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
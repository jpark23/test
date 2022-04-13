''' "New" Deadlock Detection Description:
The deadlock detection we have implemented is based on the algorithm “detecting 
simple deadlocks” from the Sokoban Wiki Page 
(http://sokobano.de/wiki/index.php?title=How_to_detect_deadlocks). 
First, we modified parse_map to store all the possible positions an object can 
be on the map within the SokobanProblem class. From there, we created an 
adjacency list representation of the map. The idea was that from each goal, 
we would pull a box to every position on the board we can pull to. Any 
“reached” position would be noted as “not a deadlock”. From here, dfs was used 
to find a path from every goal to every position on the board (dfs works as 
follows: we add the starting position to the visited array. Repeat: visit the 
first item in the array, and add all the not visited adjacent positions to the 
visited array . For each path that is then found, we validated that the path 
could be taken (by pulling a box from the start/goal) using the function 
path_valid. In this function, we iterate through the path of coordinates, and 
verify that we can pull a box from each part of the path to the next, the path 
is “valid”. Additionally, we needed another modified dfs function, dfs_pathchecker, 
to verify that there exists at least one path where we could walk around the map 
to pull the box into a new direction (dfs_pathchecker works as follows: the previous 
dfs was modified by adding a check at the beginning of function execution to see 
if the current position is in fact the destination/end position. If this is the 
case, we return true. If this is not the case, we proceed normally with dfs and 
return false if the destination/end position is never reached). If the path was 
validated, we add each coordinate in the path to a “not deadlocks” set. From there, 
we iterated through every possible position, creating the deadlocks list based on 
the fact that if a position p is not in “not-deadlocks” and the position is a valid 
position on the board, it must be a deadlock. 
'''

#from dataclasses import asdict
from json.encoder import INFINITY
from lib2to3.pgen2.pgen import NFAState
# from more_itertools import last
from numpy import Infinity
import util
import os, sys
import datetime, time
import argparse
import signal, gc
import random
import logging

sys.setrecursionlimit(1500) # changed from 2000

class SokobanState:
    # player: 2-tuple representing player location (coordinates)
    # boxes: list of 2-tuples indicating box locations
    def __init__(self, player, boxes):
        # self.data stores the state
        self.data = tuple([player] + sorted(boxes))
        # below are cache variables to avoid duplicated computation
        self.all_adj_cache = None
        self.adj = {}
        self.dead = None
        self.solved = None
    def __str__(self):
        return 'player: ' + str(self.player()) + ' boxes: ' + str(self.boxes())
    def __eq__(self, other):
        return type(self) == type(other) and self.data == other.data
    def __lt__(self, other):
        return self.data < other.data
    def __hash__(self):
        return hash(self.data)
    # return player location
    def player(self):
        return self.data[0]
    # return boxes locations
    def boxes(self):
        return self.data[1:]
    def is_goal(self, problem):
        if self.solved is None:
            self.solved = all(problem.map[b[0]][b[1]].target for b in self.boxes())
        return self.solved
    def act(self, problem, act):
        if act in self.adj: return self.adj[act]
        else:
            val = problem.valid_move(self,act)
            self.adj[act] = val
            return val
    def deadp(self, problem):
        '''
        for state 'problem':
        if there are no deadlocks, find the deadlocks
        if there are deadlocks, just return them
        '''
        if self.dead is None:
            self.dead = False
            for box in self.boxes():
                if box in problem.deadlocks:
                    self.dead = True
                    break
        return self.dead

    def all_adj(self, problem):
        if self.all_adj_cache is None:
            succ = []
            for move in 'udlr':
                valid, box_moved, nextS = self.act(problem, move)
                if valid:
                    #if box_moved:
                        #print("move " +str(move) +" moved a box")
                    succ.append((move, nextS, 1))
            #print("adding " +str(succ[0][0]) +" to all_adj_cache")
            self.all_adj_cache = succ
        return self.all_adj_cache

class MapTile:
    def __init__(self, wall=False, floor=False, target=False):
        self.wall = wall
        self.floor = floor
        self.target = target

def parse_move(move):
    if move == 'u': return (-1,0)
    elif move == 'd': return (1,0)
    elif move == 'l': return (0,-1)
    elif move == 'r': return (0,1)
    raise Exception('Invalid move character.')

class DrawObj:
    WALL = '\033[37;47m \033[0m'
    PLAYER = '\033[97;40m@\033[0m'
    BOX_OFF = '\033[30;101mX\033[0m'
    BOX_ON = '\033[30;102mX\033[0m'
    TARGET = '\033[97;40m*\033[0m'
    FLOOR = '\033[30;40m \033[0m'
    UNDERLINE = '\033[4m'
    END = '\033[0m'

class SokobanProblem(util.SearchProblem):
    # valid sokoban characters
    valid_chars = 'T#@+$*. '

    def __init__(self, map, dead_detection=False, a2=False):
        self.map = [[]]
        self.dead_detection = dead_detection
        self.init_player = (0,0)
        self.init_boxes = []
        self.numboxes = 0
        self.targets = []
        self.possible_pos, self.walls = self.parse_map(map)
        self.found_deadlocks = False
        self.deadlocks = []

    # parse the input string into game map
    # Wall              #
    # Player            @
    # Player on target  +
    # Box               $
    # Box on target     *
    # Target            .
    # Floor             (space)
    def parse_map(self, input_str):
        coordinates = lambda: (len(self.map)-1, len(self.map[-1])-1)
        possible_pos = set()
        walls = set()
        for c in input_str:
            if c == '#':
                self.map[-1].append(MapTile(wall=True))
                walls.add(coordinates())
                # print("wall @", coordinates())
            elif c == ' ':
                self.map[-1].append(MapTile(floor=True))
                if coordinates() != (0,0): 
                    possible_pos.add(coordinates())
                    # print("empty square @", coordinates())
            elif c == '@':
                self.map[-1].append(MapTile(floor=True))
                self.init_player = coordinates()
                # print("player coordinates =", coordinates())
                possible_pos.add(coordinates())
            elif c == '+':
                self.map[-1].append(MapTile(floor=True, target=True))
                self.init_player = coordinates()
                self.targets.append(coordinates())
                possible_pos.add(coordinates())
                # print("player on target @", coordinates())
            elif c == '$':
                self.map[-1].append(MapTile(floor=True))
                self.init_boxes.append(coordinates())
                # print("box coordinates =", coordinates())
                possible_pos.add(coordinates())
            elif c == '*':
                self.map[-1].append(MapTile(floor=True, target=True))
                self.init_boxes.append(coordinates())
                self.targets.append(coordinates())
                possible_pos.add(coordinates())
                # print("box on target @", coordinates())
            elif c == '.':
                self.map[-1].append(MapTile(floor=True, target=True))
                self.targets.append(coordinates())
                # print("target coordinates =", coordinates())
                possible_pos.add(coordinates())
            elif c == '\n':
                self.map.append([])
        assert len(self.init_boxes) == len(self.targets), 'Number of boxes must match number of targets.'
        self.numboxes = len(self.init_boxes)
        # self.walls = walls 
        # print("number of walls:", len(self.walls)) # print to make sure walls are instantiated
        return possible_pos, walls

    def print_state(self, s):
        for row in range(len(self.map)):
            for col in range(len(self.map[row])):
                target = self.map[row][col].target
                box = (row,col) in s.boxes()
                player = (row,col) == s.player()
                if box and target: print(DrawObj.BOX_ON, end='')
                elif player and target: print(DrawObj.PLAYER, end='')
                elif target: print(DrawObj.TARGET, end='')
                elif box: print(DrawObj.BOX_OFF, end='')
                elif player: print(DrawObj.PLAYER, end='')
                elif self.map[row][col].wall: print(DrawObj.WALL, end='')
                else: print(DrawObj.FLOOR, end='')
            print()

    # decide if a move is valid
    # return: (whether a move is valid, whether a box is moved, the next state)
    def valid_move(self, s, move, p=None):
        if p is None:
            p = s.player()
        dx,dy = parse_move(move)
        x1 = p[0] + dx
        y1 = p[1] + dy
        x2 = x1 + dx
        y2 = y1 + dy
        if self.map[x1][y1].wall:
            return False, False, None
        elif (x1,y1) in s.boxes():
            if self.map[x2][y2].floor and (x2,y2) not in s.boxes():
                return True, True, SokobanState((x1,y1),
                    [b if b != (x1,y1) else (x2,y2) for b in s.boxes()])
            else:
                return False, False, None
        else:
            return True, False, SokobanState((x1,y1), s.boxes())

    '''Problem 1
    ##############################################################################
    # Problem 1: Dead end detection                                              #
    # Modify the function below. We are calling the deadp function for the state #
    # so the result can be cached in that state. Feel free to modify any part of #
    # the code or do something different from us.                                #
    # Our solution to this problem affects or adds approximately 50 lines of     #
    # code in the file in total. Your can vary substantially from this.          #
    ##############################################################################
    '''
    def find_deadlocks(self):
        '''
        1. search only non goal floor tiles
        2. check adjacent tiles, if 1 of left and right and 1 of top and bottom is a wall
           then that tile is a corner and therefore a deadlock
        2.5 check for more deadlocks by using existing deadlocks (current problem when there is a corridor with a goal in it)
        3. append the deadlock index to self.deadlocks
        '''
        
        ##add in a second pass to find more deadlocks
        def jack_deadlock(self):
            # sys.exit("Friendly reminder to change the way we check if a state is deadlocked.\nJack's implementation finds deadlocks, Jason's finds not deadlocks")
            deadlocks = list()
            for row in range(1, len(self.map)-1):
                for col in range(1, len(self.map[row])-1):
                    if(self.map[row][col].floor and not self.map[row][col].target):
                        #tile is floor and not target, check it too see if dead end
                        #if one of left and right and one of up and down are walls then it is a corner
                        #left and right
                        try:
                            if(self.map[row-1][col].wall or self.map[row+1][col].wall):
                                if(self.map[row][col-1].wall or self.map[row][col+1].wall):
                                    deadlocks.append((row, col))
                        except IndexError: pass
            return deadlocks

        def corridor_deadlocks(self)->set:
            cdr_dl = set()
            for row in range(1, len(self.map)-1):
                for col in range(1, len(self.map[row])-1):
                    if(self.map[row][col].floor and not self.map[row][col].target and (row, col) not in self.deadlocks):
                        #search for tiles where 3/4 neighbors are walls or deadlocks, those are also deadlocks
                        try:
                            if(self.map[row][col+1].wall and self.map[row][col-1].wall): #horizontal column
                                if((row-1, col) in self.deadlocks): #negative end
                                    i = 1
                                    while(not self.map[row+i][col].target): #search down the corridor for a goal
                                        if(self.map[row+i][col].wall or (row+i, col) in self.deadlocks):
                                            # self.deadlocks.append((row,col))
                                            cdr_dl.add((row,col))
                                            break
                                        i += 1
                                elif((row+1, col) in self.deadlocks): #positive end
                                    i = 1
                                    while(not self.map[row-i][col].target): #search down the corridor for a goal
                                        if(self.map[row-i][col].wall or (row-i, col) in self.deadlocks):
                                            # self.deadlocks.append((row,col))
                                            cdr_dl.add((row,col))
                                            break
                                        i += 1
                            elif(self.map[row-1][col].wall and self.map[row+1][col].wall): #vertical column
                                if((row, col-1) in self.deadlocks): #negative end
                                    i = 1
                                    while(not self.map[row][col+i].target): #search down the corridor for a goal
                                        if(self.map[row][col+i].wall or (row, col+i) in self.deadlocks):
                                            # self.deadlocks.append((row,col))
                                            cdr_dl.add((row,col))
                                            break
                                        i += 1
                                elif((row, col+1) in self.deadlocks): #positive end
                                    i = 1
                                    while(not self.map[row][col-i].target): #search down the corridor for a goal
                                        if(self.map[row][col-i].wall or (row, col-i) in self.deadlocks):
                                            # self.deadlocks.append((row,col))
                                            cdr_dl.add((row,col))
                                            break
                                        i += 1
                        except IndexError: pass
                return cdr_dl
        
        def wall_scraper(self, jack_dl):
            def create_wall_bounds(jack_dl):
                bounds = dict()
                for dl in jack_dl:
                    bounds.update({dl: []})
                for (x,y) in bounds:
                    for (x1, y1) in jack_dl:
                        if x == x1 or y == y1: bounds[(x,y)].append((x1,y1))
                # for bound in bounds: print(bound, bounds[bound])
                return bounds

            def pos_on_wall(self, pos)->bool:
                test_pos = set()
                x,y = pos
                test_pos.add( (x,y) )
                test_pos.add( (x+1, y) )
                test_pos.add( (x-1, y) )
                test_pos.add( (x, y+1) )
                test_pos.add( (x, y-1) )
                if len(test_pos.intersection(self.walls)) >= 1: return True 
                return False 

            def fill_wall(start, end)->set:
                if start == end: return set()
                new_points = list()
                if start[0] == end[0]:
                    for pos in range(start[1], end[1]):
                        if pos_on_wall(self, (start[0], pos)): new_points.append((start[0], pos))
                elif start[1] == end[1]:
                    for pos in range(start[0], end[0]):
                        if pos_on_wall(self, (pos, start[1])): new_points.append((pos, start[1]))
                for point in new_points: 
                    if point in self.walls: new_points.remove(point)
                # if start == (1,10) and end == (4,10):
                #     print(new_points)
                #     print(len(new_points) in [abs(start[0]-end[0]), abs(start[1]-end[1])])
                #     sys.exit("stopped")
                if len(new_points) in [abs(start[0]-end[0]), abs(start[1]-end[1])]:
                    return set(new_points)
                else: return set()

            def get_points_on_wall(wall_adj)->dict:
                on_wall_points = dict()
                for corner in wall_adj:
                    for end_pos in wall_adj[corner]:
                        toAdd = fill_wall(corner, end_pos)
                        key = (corner, end_pos)
                        on_wall_points.update({key: toAdd})
                return on_wall_points

            def remove_known_dl(self, new_pot_dl)->dict:
                for key in new_pot_dl:
                    if new_pot_dl[key] == set(): new_pot_dl[key] = None
                targets = set(self.targets)
                cleaned_wall_pos = dict()
                for key in new_pot_dl:
                    if new_pot_dl[key] is not None: 
                        if new_pot_dl[key] & targets == set():
                            cleaned_wall_pos.update({key: new_pot_dl[key]})
                return cleaned_wall_pos

            wall_adj = create_wall_bounds(jack_dl)
            # for key in wall_adj: print(key, wall_adj[key])
            new_pot_dl = get_points_on_wall(wall_adj)
            new_dls = remove_known_dl(self, new_pot_dl)
            new_deadlocks = set()
            for key in new_dls:
                for new_dl in new_dls[key]:
                    if new_dl in self.possible_pos:
                        new_deadlocks.add(new_dl)
            return new_deadlocks

        def jason_deadlock(self, prev_deadlocks):
            # trying to reason out all possible valid spaces, everything else is deadlock
            if self.possible_pos is not None:
                # get adj_list
                possible_pos = self.possible_pos
                adj_list = {}
                for pos in sorted(possible_pos):
                    try: adj_list[pos]
                    except: adj_list[pos] = set()   
                    possible_adj_list = [(pos[0], pos[1]+1), (pos[0], pos[1]-1), (pos[0]+1, pos[1]), (pos[0]-1, pos[1])] 
                    for possible_adj in possible_adj_list:
                        if possible_adj in possible_pos: adj_list[pos].add(possible_adj)
            
            def dfs(adj_list, pos, visited):
                # dfs algorithm borrowed from: https://www.programiz.com/dsa/graph-dfs
                visited.append(pos)
                for adj in adj_list[pos]:
                    if adj not in visited:
                        dfs(adj_list, adj, visited.copy())
                if visited[-1] not in prev_deadlocks: paths.append(visited)
                # paths.append(visited)
                
            def dfs_pathchecker(pos, end, adj_list, visited):
                if pos == end: return True
                visited.append(pos)
                for adj in adj_list[pos]:
                    if adj not in visited:
                        if (dfs_pathchecker(adj, end, adj_list, visited)):
                            return True 
                return False

            def interpret_movement(start_pos, end_pos):
                if start_pos[0] > end_pos[0]:
                    return 'u'
                elif start_pos[0] < end_pos[0]:
                    return 'd'
                elif start_pos[1] > end_pos[1]:
                    return 'l'
                elif start_pos[1] < end_pos[1]:
                    return 'r'
                return '' 

            def do_move(pos, move):
                dx,dy = parse_move(move)
                x1 = pos[0] + dx
                y1 = pos[1] + dy
                return (x1, y1)

            def path_valid(path):
                curr_pos = None
                index = 0
                path_found = True
                while index + 1 < len(path):
                    if path_found is False: break
                    if curr_pos is None:
                        curr_pos = path[index+1]
                    start_pos = path[index]
                    end_pos = path[index+1]
                    pull_dir = interpret_movement(start_pos, end_pos)  
                    curr_pos = do_move(end_pos, pull_dir)
                    if curr_pos not in possible_pos: 
                        path_found = False
                    index += 1
                return path_found
        
            not_deadlocks = set()
            for goal_pos in self.targets:                                                                      
                paths = list()                                  
                dfs(adj_list, goal_pos, [])                     
                # print("num of paths to check:", len(paths)) # uncomment this to see how many paths are being checked
                # sys.exit("\nDeliberate Stoppage\n")
                for path in paths:                              
                    if path_valid(path): not_deadlocks |= set(path)              
            
            deadlocks = set()
            for pos in possible_pos:
                if pos not in not_deadlocks: deadlocks.add(pos)

            return deadlocks

        import time 
        # print(sorted(self.walls))
        # print(self.targets)
        # print("num possible pos:", len(self.possible_pos))
        # print("num walls:", len(self.walls))
        # print("use:", len(self.possible_pos)- len(self.walls))

        start_time_jack = time.time()
        jack_deadlocks = set(jack_deadlock(self))
        end_time_jack = time.time()
        print("jack found", len(jack_deadlocks), "deadlocks in", (end_time_jack - start_time_jack), "seconds")
        self.deadlocks = jack_deadlocks
        # print("jacks deadlocks:", sorted(jack_deadlocks))

        # cdr_start = time.time()
        # corridor_dl = corridor_deadlocks(self)
        # cdr_end = time.time()
        # just_cdr = len( corridor_dl.difference(jack_deadlocks) )
        # print("Jack also found", just_cdr, "corridor deadlocks in", (cdr_end - cdr_start), "seconds")
        # self.deadlocks = corridor_dl.union(jack_deadlocks)

        wall_dl_start = time.time()
        wall_deadlocks = wall_scraper(self, sorted(jack_deadlocks))
        wall_dl_end = time.time()
        just_walls = len( wall_deadlocks.difference(jack_deadlocks) )
        print(just_walls, "more deadlocks from wall scraping found in", (wall_dl_end - wall_dl_start), "seconds")
        self.deadlocks = wall_deadlocks.union(jack_deadlocks)
        # print("wall scraper deadlocks:", sorted(wall_deadlocks))
        # print("deadlocks from jack and wall scraping:", sorted(self.deadlocks))

        # start_time_jason = time.time()
        # jason_deadlocks = jason_deadlock(self, self.deadlocks)   # comment this
        # # jason_deadlocks = jason_deadlock(self, [])             # and uncomment this to use purely exhaustive detection
        # end_time_jason = time.time()
        # from_jason = len( jason_deadlocks.difference(self.deadlocks) )
        # print("jason found", from_jason, "more deadlocks in", (end_time_jason - start_time_jason), "seconds")
        # # print("jasons deadlocks:", sorted(jason_deadlocks))

        # self.deadlocks = jason_deadlocks.union(wall_deadlocks)
        
        return
    
    def dead_end(self, s):
        '''
        If deadlocks have not been searched for in the problem then search for deadlocks
        then send the state to deadp and check for dealocks
        currently only looking for corners as deadlocks
        '''
        if not self.dead_detection:
            # not looking for deadlocks in this test
            return False
        if(not self.found_deadlocks):
            print("\nlooking for deadlocks...")
            self.find_deadlocks()
            self.found_deadlocks = True
            print("using", len(self.deadlocks), "total deadlocks\n")
            # sys.exit("\ndeliberate stoppage\n")
            # print(self.deadlocks)
        return s.deadp(self)

    def start(self):
        return SokobanState(self.init_player, self.init_boxes)

    def goalp(self, s):
        return s.is_goal(self)

    def expand(self, s):
        if self.dead_end(s):
            return []
        return s.all_adj(self)

class SokobanProblemFaster(SokobanProblem):
    ##############################################################################
    # Problem 2: Action compression                                              #
    # Redefine the expand function in the derived class so that it overrides the #
    # previous one. You may need to modify the solve_sokoban function as well to #
    # account for the change in the action sequence returned by the search       #
    # algorithm. Feel free to make any changes anywhere in the code.             #
    # Our solution to this problem affects or adds approximately 80 lines of     #
    # code in the file in total. Your can vary substantially from this.          #
    ##############################################################################
    def expand(self, s):
        from queue import LifoQueue

        if self.dead_end(s):
            return []

        def get_box_moves_recur(self, s, pos, valid, box_moves):
            if pos in valid or self.dead_end(s):
                return
            else:
                valid.append(pos)
            for direction in 'urdl':
                isValid, isMoved, nState = self.valid_move(s, direction, p=pos)
                if isValid and isMoved and not self.dead_end(nState):
                    box_moves.append((pos, direction, nState))
                elif isValid and not isMoved and not self.dead_end(nState):
                    get_box_moves_recur(self, nState, nState.player(), valid, box_moves)

        def get_box_moves_iter(self, s, pos, valid, box_moves):
            if self.dead_end(s):
                return []
            lifo = LifoQueue()
            lifo.put((pos, s))
            while not lifo.empty():
                (node_pos, node_s) = lifo.get()
                valid.append(node_pos)
                for direction in 'urdl':
                    isValid, isMoved, nState = self.valid_move(node_s, direction, p=node_pos)
                    if  isValid and nState.player() in valid:
                        continue
                    if isValid and isMoved and not self.dead_end(nState):
                        box_moves.append((node_pos, direction, nState))
                    elif isValid and not isMoved and not self.dead_end(nState):
                        lifo.put((nState.player(), nState))

        def get_adj_spot(self, s, pos) -> list:
            valid = []
            #adjacents = [(pos[0]+1, pos[1]), (pos[0]-1, pos[1]), (pos[0], pos[1]+1), (pos[0], pos[1]-1)]
            #valid_move(self, s, move, p=None):
            for direction in 'urdl':
                isValid, isMoved, nState = self.valid_move(s, direction, p=pos)
                if (isValid):
                    valid.append((pos, direction, nState, isMoved))
            return valid
        
        def interpret_movement(start_pos, end_pos):
            if start_pos[0] > end_pos[0]:
                return 'd'
            elif start_pos[0] < end_pos[0]:
                return 'u'
            elif start_pos[1] > end_pos[1]:
                return 'r'
            elif start_pos[1] < end_pos[1]:
                return 'l'
            return ''  
        
        def find_path(self, s, start_pos):
            dist = dict()
            previous = dict()
            pq = dict()
            # add all valid tiles
            #valid_tiles = list()
            #box_moves = list()
            # get_box_moves_iter(self, s, start_pos, valid_tiles, box_moves)
            # get_box_moves_recur(self, s, start_pos, valid_tiles, box_moves)
            # for spot in valid_tiles:
            #     dist[spot] = INFINITY
            #     previous[spot] = None
            #     pq[spot] = INFINITY
            box_moves = list()#(pos, direction, nState)
            dist[start_pos] = 0
            pq[start_pos] = 0
            previous[start_pos] = None
            removed = dict()
            # djikstras
            while len(pq) > 0:
                
                u = min(pq, key=pq.get)
                pq.pop(u)
                removed[u] = True
                neighbors = list()
                #valid_move(self, s, move, p=None):
                #adj = (pos, direction, nState, isMoved)

                for adj in get_adj_spot(self, s, u):
                    #print(adj)
                    if adj[3] == True:
                        if not self.dead_end(adj[2]):
                            box_moves.append((adj[0], adj[1], adj[2]))
                    else:
                        spot = adj[2].player()
                        if spot not in removed:
                            neighbors.append(spot)
                        if spot not in dist:
                            dist[spot] = INFINITY
                            previous[spot] = None
                            pq[spot] = INFINITY
                # print("------------------")
                # print("PQ",pq)
                # print("DIST", "PREV", "MOVES", dist, previous, box_moves)
                # print("SPOT", u)
                # print("NEIGH", neighbors)
                # print("------------------")
                # sys.exit()

                for v in neighbors:
                    temp = dist[u] + 1
                    if temp < dist[v]:
                        dist[v] = temp
                        previous[v] = u
                        pq[v] = temp
            return (dist, previous, box_moves)
        
        def trace_path(self, s, start_pos, end_pos, previous):
            # get traceback from endpos
            path = ""
            curr = end_pos
            while previous[curr] != None and curr != start_pos:
                mvmt = interpret_movement(curr, previous[curr])
                path  = mvmt + path
                curr = previous[curr]
            return path
            
        (dist, previous, moves) = find_path(self, s, s.player())
        expand_actions = []
        for move in moves:
            path = trace_path(self, s, s.player(), move[0], previous) + move[1]
            expand_actions.append((path, move[2], 1))

        return expand_actions # action, newState, cost

class Heuristic:
    def __init__(self, problem):
        self.problem = problem
        self.values = None
        self.closest_target = dict()

    ##############################################################################
    # Problem 3: Simple admissible heuristic                                     #
    # Implement a simple admissible heuristic function that can be computed      #
    # quickly based on Manhattan distance. Feel free to make any changes         #
    # anywhere in the code.                                                      #
    # Our solution to this problem affects or adds approximately 10 lines of     #
    # code in the file in total. Your can vary substantially from this.          #
    ##############################################################################
    def heuristic(self, s):
        #raise NotImplementedError('Override me')
        def calculate_closest_target(self, s, pos):
            closest_dist = float('inf')
            for goal in self.problem.targets:
                dist = abs(goal[0]-pos[0]) + abs(goal[1]-pos[1])
                if(dist < closest_dist): closest_dist = dist
            self.closest_target[pos] = closest_dist
            return closest_dist
        total_dist = 0
        for box in s.boxes():
            if ((box[0], box[1]) in self.closest_target):
                total_dist += self.closest_target[(box[0], box[1])]
            else:
                total_dist += calculate_closest_target(self, s, box)
        #print("total dist is " +str(total_dist))
        return total_dist

    ##############################################################################
    # Problem 4: Better heuristic.                                               #
    # Implement a better and possibly more complicated heuristic that need not   #
    # always be admissible, but improves the search on more complicated Sokoban  #
    # levels most of the time. Feel free to make any changes anywhere in the     #
    # code. Our heuristic does some significant work at problem initialization   #
    # and caches it.                                                             #
    # Our solution to this problem affects or adds approximately 40 lines of     #
    # code in the file in total. Your can vary substantially from this.          #
    ##############################################################################
    def heuristic2(self, s):
        #raise NotImplementedError('Override me')
        if(self.values == None):
            print("doing initial calculations")
            costs = []
            for row in range(len(self.problem.map)):
                costs.append([])#add a new row
                for col in range(len(self.problem.map[row])):
                    ##see if floor tiles can reach goal tiles
                    #out = "tile "+str(row)+" "+str(col)+" is a "
                    if(self.problem.map[row][col].floor):
                        costs[-1].append(1)
                        #out += "floor "
                    if(self.problem.map[row][col].wall):
                        costs[-1].append(999)
                        #out += "wall "
                    if(self.problem.map[row][col].target):
                        costs[-1].append(0)
                        #out += "target "
                    #print(out)
            print(costs)
            self.values = costs
        total = 0
        for box in s.boxes():
            #print(box)
            total += self.values[box[0]][box[1]]
        #print(total)
        #sys.exit()
        return total
    
# solve sokoban map using specified algorithm
#  algorithm can be ucs a a2 fa fa2
def solve_sokoban(map, algorithm='ucs', dead_detection=False):
    # problem algorithm
    if algorithm == 'c':
        dead_detection = True
        algorithm = 'fa'
    if 'f' in algorithm:
        problem = SokobanProblemFaster(map, dead_detection, '2' in algorithm)
    else:
        problem = SokobanProblem(map, dead_detection, '2' in algorithm)

    # search algorithm
    h = Heuristic(problem).heuristic2 if ('2' in algorithm) else Heuristic(problem).heuristic
    if 'a' in algorithm:
        search = util.AStarSearch(heuristic=h)
    else:
        search = util.UniformCostSearch()

    # solve problem
    search.solve(problem)
    if search.actions is not None:
        print('length {} soln is {}'.format(len(search.actions), search.actions))
    if 'f' in algorithm:
        return search.totalCost, search.actions, search.numStatesExplored
        raise NotImplementedError('Override me')
    else:
        if(search.actions == None):
            print("search.actions is None")
            search.actions = ['u', 'u', 'd', 'd', 'l', 'r', 'l', 'r']
        return search.totalCost, search.actions, search.numStatesExplored

# animate the sequence of actions in sokoban map
def animate_sokoban_solution(map, seq, dt=0.2):
    problem = SokobanProblem(map)
    state = problem.start()
    clear = 'cls' if os.name == 'nt' else 'clear'
    for i in range(len(seq)):
        os.system(clear)
        print(seq[:i] + DrawObj.UNDERLINE + seq[i] + DrawObj.END + seq[i+1:])
        problem.print_state(state)
        time.sleep(dt)
        valid, _, state = problem.valid_move(state, seq[i])
        if not valid:
            raise Exception('Cannot move ' + seq[i] + ' in state ' + str(state))
    os.system(clear)
    print(seq)
    problem.print_state(state)

# read level map from file, returns map represented as string
def read_map_from_file(file, level):
    map = ''
    start = False
    found = False
    with open(file, 'r') as f:
        for line in f:
            if line[0] == "'": continue
            if line.strip().lower()[:5] == 'level':
                if start: break
                if line.strip().lower() == 'level ' + level:
                    found = True
                    start = True
                    continue
            if start:
                if line[0] in SokobanProblem.valid_chars:
                    map += line
                else: break
    if not found:
        raise Exception('Level ' + level + ' not found')
    return map.strip('\n')

# extract all levels from file
def extract_levels(file):
    levels = []
    with open(file, 'r') as f:
        for line in f:
            if line.strip().lower()[:5] == 'level':
                levels += [line.strip().lower()[6:]]
    return levels

def extract_timeout(file, level):
    start = False
    found = False
    with open(file, 'r') as f:
        for line in f:
            if line[0] == "'": continue
            if line.strip().lower()[:5] == 'level':
                if start: break
                if line.strip().lower() == 'level ' + level:
                    found = True
                    continue
            if found:
                if line.strip().lower()[:7] == 'timeout':
                    return(int(line.strip().lower()[8:]))
                else: break
    if not found:
        raise Exception('Level ' + level + ' not found')
    return None

def solve_map(file, level, algorithm, dead, simulate):
    map = read_map_from_file(file, level)
    print(map)
    if dead: print('Dead end detection on for solution of level {level}'.format(**locals()))
    tic = datetime.datetime.now()
    cost, sol, nstates = solve_sokoban(map, algorithm, dead)
    toc = datetime.datetime.now()
    print('Time consumed: {:.3f} seconds using {} and exploring {} states'.format(
        (toc - tic).seconds + (toc - tic).microseconds/1e6, algorithm, nstates))
    seq = ''.join(sol)
    print(len(seq), 'moves')
    print(' '.join(seq[i:i+5] for i in range(0, len(seq), 5)))
    if simulate:
        animate_sokoban_solution(map, seq)

def main():
    parser = argparse.ArgumentParser(description="Solve Sokoban map")
    parser.add_argument("level", help="Level name or 'all'")
    parser.add_argument("algorithm", help="ucs | [f][a[2]] | all")
    parser.add_argument("-d", "--dead", help="Turn on dead state detection (default off)", action="store_true")
    parser.add_argument("-s", "--simulate", help="Simulate the solution (default off)", action="store_true")
    parser.add_argument("-f", "--file", help="File name storing the levels (levels.txt default)", default='levels.txt')
    parser.add_argument("-t", "--timeout", help="Seconds to allow (default 300) (ignored if level specifies)", type=int, default=300)

    args = parser.parse_args()
    level = args.level
    algorithm = args.algorithm
    dead = args.dead
    simulate = args.simulate
    file = args.file
    maxSeconds = args.timeout

    if (algorithm == 'all' and level == 'all'):
        raise Exception('Cannot do all levels with all algorithms')

    def solve_now(): solve_map(file, level, algorithm, dead, simulate)

    def solve_with_timeout(timeout):
        level_timeout = extract_timeout(file,level)
        if level_timeout != None: timeout = level_timeout

        try:
            util.TimeoutFunction(solve_now, timeout)()
        except KeyboardInterrupt:
            raise
        except MemoryError as e:
            signal.alarm(0)
            gc.collect()
            print('Memory limit exceeded.')
        except util.TimeoutFunctionException as e:
            signal.alarm(0)
            print('Time limit (%s seconds) exceeded.' % timeout)

    if level == 'all':
        levels = extract_levels(file)
        for level in levels:
            print('Starting level {}'.format(level), file=sys.stderr)
            sys.stdout.flush()
            solve_with_timeout(maxSeconds)
    elif algorithm == 'all':
        for algorithm in ['ucs', 'a', 'a2', 'f', 'fa', 'fa2']:
            print('Starting algorithm {}'.format(algorithm), file=sys.stderr)
            sys.stdout.flush()
            solve_with_timeout(maxSeconds)
    else:
        solve_with_timeout(maxSeconds)

if __name__ == '__main__':
    main()
#!/usr/bin/env python
import sys
import traceback
import random as rnd
import time
from collections import defaultdict
from math import sqrt
from numpy import *
from scipy.signal import convolve2d
import logging
set_printoptions(precision=3,threshold=200*200,linewidth=200*10)

MY_ANT = 0
ANTS = 0
DEAD = -1
LAND = -2
FOOD = -3
WATER = -4

PLAYER_ANT = 'abcdefghij'
HILL_ANT = string = 'ABCDEFGHI'
PLAYER_HILL = string = '0123456789'
MAP_OBJECT = '?%*.!'
MAP_RENDER = PLAYER_ANT + HILL_ANT + PLAYER_HILL + MAP_OBJECT

AIM = {'n': (-1, 0),
       'e': (0, 1),
       's': (1, 0),
       'w': (0, -1)}
RIGHT = {'n': 'e',
         'e': 's',
         's': 'w',
         'w': 'n'}
LEFT = {'n': 'w',
        'e': 'n',
        's': 'e',
        'w': 's'}
BEHIND = {'n': 's',
          's': 'n',
          'e': 'w',
          'w': 'e'}

class Ants():
	def __init__(self):
		self.cols = None
		self.rows = None
		self.map = None
		self.hill_list = {}
		self.ant_list = {}
		self.dead_list = defaultdict(list)
		self.food_list = []
		self.turntime = 0
		self.loadtime = 0
		self.turn_start_time = None
		self.vision = None
		self.enemyVision = None
		self.viewradius2 = 0
		self.attackradius2 = 0
		self.spawnradius2 = 0
		self.turns = 0

		Dfood=Dexplore=0.1#max 0.25 
		DenemyHill=0.2
		self.foodKernelMax=self.exploreKernelMax=1-4*Dfood
		self.enemyHillKernelMax=1-4*DenemyHill
		self.enemyHillKernel=array([[0,DenemyHill,0],[DenemyHill,self.enemyHillKernelMax,DenemyHill],[0,DenemyHill,0]])
		self.foodKernel=array([[0,Dfood,0],[Dfood,self.foodKernelMax,Dfood],[0,Dfood,0]])
		self.exploreKernel=self.foodKernel		
		DquorumScent=0.12#max 0.14
		self.quorumScentKernelMax=1-6.8*DquorumScent#based on corners being sqrt(2) dist 1-4D-(4D/1.4)
		self.quorumScentKernel=array([[DquorumScent/1.4,DquorumScent,DquorumScent/1.4],[DquorumScent,self.quorumScentKernelMax,DquorumScent],[DquorumScent/1.4,DquorumScent,DquorumScent/1.4]])

		self.vision_offsets_2=None
		self.attackOffsets2=None
		self.aVisible=None
		self.aUnseen=None
		self.waterMap=None
		self.blockMap=None
		self.antMaps=[]
		self.attackRadiusMaps=[]
		self.friendsMap=None
		self.armies=[]
		self.nOfEnemies=-1
		self.mapFullyExplored=False
		self.enemyHillsList=[]
		self.myAnts=[]
		self.enemyAnts=[]
		self.foodGradient=None
		self.exploreGradient=None
		self.quorumDecisionGradient=None
		self.attackGradient=None
		self.armyGradient=None
		self.enemyHillGradients={}
		self.unifiedEnemyHillsGradeint=None
		self.defenseGradient=None
		self.defenseGradientMax=1
		self.defensiveness=1.5
		self.spareAntCount_Fort=0
		self.explorerAntBuffer_Fort=10
		self.spareAntCount=0

	class Army():
		def __init__(self,route,armySize,waterMap,myAntsMap):
			Darmy=0.2#max 0.25 
			self.armyKernelMax=1-4*Darmy
			self.armyKernel=array([[0,Darmy,0],[Darmy,self.armyKernelMax,Darmy],[0,Darmy,0]])
			self.route=route
			self.armySize=armySize
			self.waterMap=waterMap
			self.routeIndex=0
			self.myAntsMap=myAntsMap
			self.mapSize=shape(self.waterMap)

			self.fillArmyGradient(self.routeIndex,self.waterMap)
			
		def fillArmyGradient(self,routeIndex,waterMap):
			loc=self.route[routeIndex]
			logging.debug(loc)
			self.armyGradient=zeros(self.mapSize)
			filled=[loc]
			fringe=[loc]
			self.armyGradient[loc]=1
			size=1
			while size < self.armySize:
				exploreNode=fringe[0]
				fringe.pop(0)
				for drxn in 'nesw':
					probeDest=self.destination(exploreNode,drxn)
					if self.waterMap[probeDest] and probeDest not in filled:
						filled.append(probeDest)
						fringe.append(probeDest)
						self.armyGradient[probeDest]=1
						size+=1
			#diffuse the army gradient
			for i in range(3):
				self.armyGradient=convolve2d(self.armyGradient,self.armyKernel,boundary='wrap')[1:self.mapSize[0]+1,1:self.mapSize[1]+1]
				self.armyGradient=self.armyGradient*self.waterMap


		def destination(self, loc, direction):
			'calculate a new location given the direction and wrap correctly'
			row, col = loc
			d_row, d_col = AIM[direction]
			return ((row + d_row) % self.mapSize[0], (col + d_col) % self.mapSize[1])        

		def marchForward(self):
			self.routeIndex+=1
			if self.routeIndex>=len(self.route): return 'reached';logging.debug('reached')
			if sum(self.armyGradient*self.myAntsMap) < self.armySize/2:return 'stationary';logging.debug('stationary')
			logging.debug(self.routeIndex)
			logging.debug(self.route)
			self.fillArmyGradient(self.routeIndex,self.waterMap)

	def setup(self, data):
		'parse initial input and setup starting game state'
		for line in data.split('\n'):
		   line = line.strip().lower()
		   if len(line) > 0:
				tokens = line.split()
				key = tokens[0]
				if key == 'cols':
					self.cols = int(tokens[1])
				elif key == 'rows':
					self.rows = int(tokens[1])
				elif key == 'player_seed':
					rnd.seed(int(tokens[1]))
				elif key == 'turntime':
					self.turntime = int(tokens[1])
				elif key == 'loadtime':
					self.loadtime = int(tokens[1])
				elif key == 'viewradius2':
					self.viewradius2 = int(tokens[1])
				elif key == 'attackradius2':
					self.attackradius2 = int(tokens[1])
				elif key == 'spawnradius2':
					self.spawnradius2 = int(tokens[1])
				elif key == 'turns':
					self.turns = int(tokens[1])
		self.map = [[LAND for col in range(self.cols)] for row in range(self.rows)]
		self.size=(self.rows,self.cols)
		self.setVisionOffsets()
		self.setAttackOffsets()
		self.aUnseen=ones(self.size,dtype=int)
		self.waterMap=ones(self.size,dtype=int)
		self.foodGradient=zeros(self.size,dtype=float32)
		self.exploreGradient=ones((self.size),dtype=float32)
		self.armyGradient=zeros(self.size)
		self.friendsMap=zeros(self.size,dtype=int)
#		self.attackGradient=zeros(self.size)

	def update(self, data):
		'parse engine input and update the game state'
		# start timer
		self.turn_start_time = time.time()

		# reset vision
		self.vision = None
		self.aVisible=zeros(self.size,dtype=int)
		self.friendsMap=zeros(self.size,dtype=int)
		self.defenseGradient=zeros(self.size)
		for i in range(len(self.antMaps)):
			self.antMaps[i]=zeros(self.size,dtype=int)
		for i in range(len(self.attackRadiusMaps)):
			self.attackRadiusMaps[i]=zeros(self.size,dtype=int)
		#logging.debug((' aR',self.antMaps))

		# clear hill, ant and food data
		self.hill_list = {}
		for row, col in self.ant_list.keys():
			self.map[row][col] = LAND
		self.ant_list = {}
		for row, col in self.dead_list.keys():
			self.map[row][col] = LAND
		self.dead_list = defaultdict(list)
		for row, col in self.food_list:
			self.map[row][col] = LAND
		self.food_list = []
		self.myAnts=[]
		self.enemyAnts=[]
        
		# update map and create new ant and food lists
		#logging.debug(self.nOfEnemies)
		for line in data.split('\n'):
			line = line.strip().lower()
			if len(line) > 0:
				tokens = line.split()
				if len(tokens) >= 3:
					row = int(tokens[1])
					col = int(tokens[2])
					if tokens[0] == 'w':
						self.map[row][col] = WATER
						self.waterMap[row,col]=0
					elif tokens[0] == 'f':
						self.map[row][col] = FOOD
						self.food_list.append((row, col))
						self.foodGradient[row,col]=self.foodKernelMax
					else:
						owner = int(tokens[3])
						if tokens[0] == 'a':
							if owner > self.nOfEnemies:
								self.nOfEnemies+=1
								self.antMaps.append(zeros((self.rows,self.cols),dtype=int))
								self.attackRadiusMaps.append(zeros(self.size,dtype=int))
							self.antMaps[owner][row,col]=1
							self.map[row][col] = owner
							self.ant_list[(row, col)] = owner
							if owner == MY_ANT:
								self.myAnts.append((row,col))
								for vRow, vCol in self.vision_offsets_2:
									self.aVisible[row + vRow][col + vCol] = 1
								for rH,cH in [(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1)]:
									self.friendsMap[(row+rH)%self.rows,(col+cH)%self.cols]+=1#Needs renaming
							else:
								self.enemyAnts.append((row,col))
							for rA,cA in self.attackOffsets2:
									self.attackRadiusMaps[owner][row+rA,col+cA]+=1#needs renaming
									#logging.debug(('owner,attacradiusMapPos',owner,self.attackRadiusMaps[owner][row+rA,col+cA]))
						elif tokens[0] == 'd':
							# food could spawn on a spot where an ant just died
							# don't overwrite the space unless it is land
							if self.map[row][col] == LAND:
								self.map[row][col] = DEAD
							# but always add to the dead list
							self.dead_list[(row, col)].append(owner)
						elif tokens[0] == 'h':
							owner = int(tokens[3])
							if owner > self.nOfEnemies:
								self.nOfEnemies+=1#u see the hill but not necessarily an ant
								self.antMaps.append(zeros((self.rows,self.cols),dtype=int))
								self.attackRadiusMaps.append(zeros(self.size,dtype=int))
							self.hill_list[(row, col)] = owner
		#update blockmap and other gradient essentials
		self.aUnseen=array((self.aUnseen-self.aVisible)>0,dtype=int)
		self.foodBlockMap=(1-self.aUnseen)*(1-self.antMaps[0])*self.waterMap
		self.exploreBlockMap=(1-self.aUnseen)*self.waterMap
		self.diffuseFoodGradient()
		self.findQuorumDecisionGradient()
		self.exploredFraction=sum(self.aUnseen)/(self.rows*self.cols)
		if not self.mapFullyExplored:
			self.diffuseExploreGradient()
		self.updateEnemyHills()
		self.spareAntCount=len(self.myAnts)-len(self.food_list)-len(self.enemyAnts)
		self.spareAntCount_Fort=self.spareAntCount-self.explorerAntBuffer_Fort
#		logging.debug(('spareAntCount_Fort',self.spareAntCount_Fort))
		self.findDefenseGradient()
#		for army in self.armies:
#			status=army.marchForward()
#			self.armyGradient+=army.armyGradient
		#logging.debug(self.nOfEnemies)


	def diffuseFoodGradient(self):
		if len(self.my_hills())<1: #dont collect food  when u dont have anthills
			self.foodGradient=zeros(self.size)
			return
		for i in range(7):
			self.foodGradient=convolve2d(self.foodGradient,self.foodKernel,boundary='wrap')[1:self.rows+1,1:self.cols+1]
			self.foodGradient=self.foodGradient*self.foodBlockMap

	def diffuseExploreGradient(self):
		self.exploreGradient=0.5*(self.exploreGradient+self.aUnseen)#0.5 for not incresing the numbers over turns. exploreGrad for the diffusion smell to spread
		for i in range(3):
			self.exploreGradient=convolve2d(self.exploreGradient,self.exploreKernel,boundary='wrap')[1:self.rows+1,1:self.cols+1]
			self.exploreGradient=self.exploreGradient*self.exploreBlockMap
		if self.exploredFraction>0.9:
			self.mapFullyExplored=True
			#self.exploreGradient=zeros(self.size)

	def findNearestEnemyAnt(self,loc):
		distances=[]
		for ant in self.enemyAnts:
			distances.append((self.distance(ant,loc),ant))
		return min(distances)[1]

	def findDefenseGradient(self):
		fortDirections=['nw','ne','sw','se']
		for hill in self.my_hills():
			minars={'nw':((hill[0]-1)%self.rows,(hill[1]-1)%self.cols),
					  'ne':((hill[0]-1)%self.rows,(hill[1]+1)%self.cols),
					  'sw':((hill[0]+1)%self.rows,(hill[1]-1)%self.cols),
					  'se':((hill[0]+1)%self.rows,(hill[1]+1)%self.cols)}

			haveSpare=self.spareAntCount_Fort>4*len(self.my_hills())
#			logging.debug(self.spareAntCount_Fort)
			for fortDrxn in fortDirections:
				if haveSpare and self.waterMap[minars[fortDrxn]]:
					self.defenseGradient[minars[fortDrxn]]+=self.defenseGradientMax

			if len(self.enemyAnts)==0:return
			enemy=self.findNearestEnemyAnt(hill)
			if self.distance(enemy,hill)<self.defensiveness*sqrt(self.viewradius2):
				drxn=self.direction(hill,enemy)
				for component in drxn:
					for fortDrxn in fortDirections:
						if (component in fortDrxn) and self.waterMap[minars[fortDrxn]]:
							self.defenseGradient[minars[fortDrxn]]+=self.defenseGradientMax

	def findQuorumDecisionGradient(self):
		enemyScent=zeros(self.size)
		for i in range(1,len(self.antMaps)):
			enemyScent+=self.antMaps[i]
		for i in range(7):
			enemyScent=convolve2d(enemyScent,self.quorumScentKernel,boundary='wrap')[1:self.rows+1,1:self.cols+1]
			enemyScent=enemyScent*self.waterMap

		#myHelpMap=self.attackRadiusMaps[0]
		enemyAttackMap=zeros(self.size,dtype=int)
		for i in range(1,len(self.attackRadiusMaps)):
			enemyAttackMap+=self.attackRadiusMaps[i]

		victoryMap=array((self.friendsMap-enemyAttackMap)>0,dtype=int)*array(enemyAttackMap>0,dtype=int)
		self.quorumDecisionGradient=(array(enemyAttackMap==0,dtype=int)+victoryMap)*enemyScent
		#logging.debug(victoryMap)
		#logging.debug(self.quorumDecisionGradient)

	def updateEnemyHills(self):
		for permHill in self.enemyHillsList[:]:
			if permHill not in self.enemy_hills() and self.aVisible[permHill[0]]:
				self.enemyHillsList.remove(permHill)
				self.enemyHillGradients.pop(permHill)
		for hill in self.enemy_hills():
			if hill not in self.enemyHillsList:
				self.enemyHillsList.append(hill)
				self.enemyHillGradients[hill]=zeros(self.size)
		self.diffuseEnemyHillGradients()
#				nearestAnt=self.findNearestAnt(hill[0])
#				myNearestHill=self.findMyNearestHill(nearestAnt)
#				logging.debug(('nearestAnt,nearestHill',nearestAnt,myNearestHill))
#				route=self.findAstarRoute(myNearestHill,nearestAnt)
#				route=route[len(route)/4:] # dont let them know where you are by your behaviour
#				self.armies.append(self.Army(route,5,self.waterMap,self.antMaps[0]))
		
	def diffuseEnemyHillGradients(self):
		self.unifiedEnemyHillsGradient=zeros(self.size,dtype=float32)
		for hill in self.enemyHillGradients:
			gradient=self.enemyHillGradients[hill]
			gradient[hill[0]]=self.enemyHillKernelMax
			for i in range(3):
				gradient=convolve2d(gradient,self.enemyHillKernel,boundary='wrap')[1:self.rows+1,1:self.cols+1]
				gradient=gradient*self.waterMap
			gradient[hill[0]]=5*self.enemyHillKernelMax#to take care of weird ants not taking hill behaviour)
			self.enemyHillGradients[hill]=gradient
			self.unifiedEnemyHillsGradient+=gradient
		#logging.debug(('updateEnemyHills:enemyHillGrads',self.enemyHillGradients))
	

	def findNearestAnt(self,loc):
		distances=[]
		for ant in self.myAnts:
			distances.append((self.distance(ant,loc),ant))
		return min(distances)[1]

	def findMyNearestHill(self,loc):
		distances=[]
		for hill in self.my_hills():
			distances.append((self.distance(hill,loc),hill))
		return min(distances)[1]

	def findAstarRoute(self,loc,dest):
		explored=[loc]
		fringe=[(self.distance(loc,dest)-1,[],loc)]#g+h,route,location
		exploreNode=fringe[0]
		while exploreNode[2]!=dest:
			fringe.sort()
			exploreNode=fringe[0]
			fringe.pop(0)
			for drxn in ['n','e','w','s']:
				probeDest=self.destination(exploreNode[2],drxn)
				if self.waterMap[probeDest] and (not self.aUnseen[probeDest]) and probeDest not in explored:
					probeRoute=exploreNode[1]+[probeDest]
					explored.append(probeDest)
					g=len(probeRoute) #path length
					h=self.distance(probeDest,dest)-1 #heuristic
					fringe.append([g+h,probeRoute,probeDest])
				#if probeDest in fringe:
					#if gProbe+hProbe	 > fringe[0]
		return exploreNode[1]

	def setVisionOffsets(self):
		self.vision_offsets_2 = []
		mx = int(sqrt(self.viewradius2))
		for d_row in range(-mx,mx+1):
			for d_col in range(-mx,mx+1):
				d = d_row**2 + d_col**2
				if d <= self.viewradius2:
					self.vision_offsets_2.append((
						# Create all negative offsets so vision will
						# wrap around the edges properly
						(d_row % self.rows) - self.rows,
						(d_col % self.cols) - self.cols
					))

	def setAttackOffsets(self):
		self.attackOffsets2 = []
		safeRadius2=self.attackradius2+2*int(sqrt(self.attackradius2))+1
		mx = int(sqrt(self.attackradius2))+1
		for d_row in range(-mx,mx+1):
			for d_col in range(-mx,mx+1):
				d = d_row**2 + d_col**2
				if d <= safeRadius2:
					self.attackOffsets2.append((
						# Create all negative offsets so vision will
						# wrap around the edges properly
						(d_row % self.rows) - self.rows,
						(d_col % self.cols) - self.cols
					))


	def time_remaining(self):
		return self.turntime - int(1000 * (time.time() - self.turn_start_time))
    
	def issue_order(self, order):
		'issue an order by writing the proper ant location and direction'
		(row, col), direction = order
		sys.stdout.write('o %s %s %s\n' % (row, col, direction))
		sys.stdout.flush()
		
	def finish_turn(self):
		'finish the turn by writing the go line'
		sys.stdout.write('go\n')
		sys.stdout.flush()

	def my_hills(self):
		return [loc for loc, owner in self.hill_list.items()
				if owner == MY_ANT]

	def enemy_hills(self):
		return [(loc, owner) for loc, owner in self.hill_list.items()
				if owner != MY_ANT]
		
	def my_ants(self):
		'return a list of all my ants'
		return [(row, col) for (row, col), owner in self.ant_list.items()
				if owner == MY_ANT]

	def enemy_ants(self):
		'return a list of all visible enemy ants'
		return [((row, col), owner)
				for (row, col), owner in self.ant_list.items()
				if owner != MY_ANT]

	def food(self):
		'return a list of all food locations'
		return self.food_list[:]

	def passable(self, loc):
		'true if not water'
		row, col = loc
		return self.map[row][col] != WATER

	def unoccupied(self, loc):
		'true if no ants are at the location'
		row, col = loc
		return self.map[row][col] in (LAND, DEAD)

	def destination(self, loc, direction):
		'calculate a new location given the direction and wrap correctly'
		if direction=='p':return loc
		row, col = loc
		d_row, d_col = AIM[direction]
		return ((row + d_row) % self.rows, (col + d_col) % self.cols)        

	def distance(self, loc1, loc2):
		'calculate the closest distance between to locations'
		row1, col1 = loc1
		row2, col2 = loc2
		d_col = min(abs(col1 - col2), self.cols - abs(col1 - col2))
		d_row = min(abs(row1 - row2), self.rows - abs(row1 - row2))
		return d_row + d_col

	def direction(self, loc1, loc2):
		'determine the 1 or 2 fastest (closest) directions to reach a location'
		row1, col1 = loc1
		row2, col2 = loc2
		height2 = self.rows//2
		width2 = self.cols//2
		d = []
		if row1 < row2:
			if row2 - row1 >= height2:
				d.append('n')
			if row2 - row1 <= height2:
				d.append('s')
		if row2 < row1:
			if row1 - row2 >= height2:
				d.append('s')
			if row1 - row2 <= height2:
				d.append('n')
		if col1 < col2:
			if col2 - col1 >= width2:
				d.append('w')
			if col2 - col1 <= width2:
				d.append('e')
		if col2 < col1:
			if col1 - col2 >= width2:
				d.append('e')
			if col1 - col2 <= width2:
				d.append('w')
		return d

	def visible(self, loc):
		' determine which squares are visible to the given player '

		if self.vision == None:
			if not hasattr(self, 'vision_offsets_2'):
				# precalculate squares around an ant to set as visible
				self.vision_offsets_2 = []
				mx = int(sqrt(self.viewradius2))
				for d_row in range(-mx,mx+1):
					for d_col in range(-mx,mx+1):
						d = d_row**2 + d_col**2
						if d <= self.viewradius2:
							self.vision_offsets_2.append((
								# Create all negative offsets so vision will
								# wrap around the edges properly
								(d_row % self.rows) - self.rows,
								(d_col % self.cols) - self.cols
							))
			# set all spaces as not visible
			# loop through ants and set all squares around ant as visible
			self.vision = [[False]*self.cols for row in range(self.rows)]
			for ant in self.my_ants():
				a_row, a_col = ant
				for v_row, v_col in self.vision_offsets_2:
					self.vision[a_row + v_row][a_col + v_col] = True
		row, col = loc
		return self.vision[row][col]
    
	def visibleArr(self):
		' determine which squares are visible to the given player '

		if self.vision == None:
			if not hasattr(self, 'vision_offsets_2'):
				# precalculate squares around an ant to set as visible
				self.vision_offsets_2 = []
				mx = int(sqrt(self.viewradius2))
				for d_row in range(-mx,mx+1):
					for d_col in range(-mx,mx+1):
						d = d_row**2 + d_col**2
						if d <= self.viewradius2:
							self.vision_offsets_2.append((
								# Create all negative offsets so vision will
								# wrap around the edges properly
								(d_row % self.rows) - self.rows,
								(d_col % self.cols) - self.cols
							))
			# set all spaces as not visible
			# loop through ants and set all squares around ant as visible
			self.vision = [[False]*self.cols for row in range(self.rows)]
			for ant in self.my_ants():
				a_row, a_col = ant
				for v_row, v_col in self.vision_offsets_2:
					self.vision[a_row + v_row][a_col + v_col] = True
		#row, col = loc
		return self.vision

	def render_text_map(self):
		'return a pretty string representing the map'
		tmp = ''
		for row in self.map:
			tmp += '# %s\n' % ''.join([MAP_RENDER[col] for col in row])
		return tmp

	def distance2(self, loc1, loc2):
		'calculate the closest distance between to locations'
		row1, col1 = loc1
		row2, col2 = loc2
		d_col = min(abs(col1 - col2), self.cols - abs(col1 - col2))
		d_row = min(abs(row1 - row2), self.rows - abs(row1 - row2))
		return d_row,d_col
		

	# static methods are not tied to a class and don't have self passed in
	# this is a python decorator
	@staticmethod
	def run(bot):
		'parse input, update game state and call the bot classes do_turn method'
		ants = Ants()
		map_data = ''
		while(True):
			try:
				current_line = sys.stdin.readline().rstrip('\r\n') # string new line char
				if current_line.lower() == 'ready':
					ants.setup(map_data)
					bot.do_setup(ants)
					ants.finish_turn()
					map_data = ''
				elif current_line.lower() == 'go':
					ants.update(map_data)
					# call the do_turn method of the class passed in
					bot.do_turn(ants)
					ants.finish_turn()
					map_data = ''
				else:
					map_data += current_line + '\n'
			except EOFError:
				break
			except KeyboardInterrupt:
				raise
			except:
				# don't raise error or return so that bot attempts to stay alive
				traceback.print_exc(file=sys.stderr)
				sys.stderr.flush()

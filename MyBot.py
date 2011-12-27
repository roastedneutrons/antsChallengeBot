#!/usr/bin/env python
from ants import *
#import random
import logging
from numpy import *
from scipy.signal import convolve2d

#set_printoptions(precision=3,threshold=128*128,linewidth=128*10)


class MyBot:
	def __init__(self):
#		logging.basicConfig(filename='log.txt',level=logging.DEBUG)
		self.turn=0

	def do_setup(self, a):
		# initialize data structures after learning the game settings
		pass

	def do_turn(self, a):
		def sigmoid(x):
			#x=float(x)
			return 1/(1+exp(-x))
		self.turn+=1
		f=1#food co-eff
		ex=sigmoid(a.spareAntCount)#explore co-eff 0.1
		q=2#quorumDecision co-eff
		eH=2#enemyHill co-eff
		d=4#defense co-eff
		self.unifiedGradient=f*a.foodGradient+ex*a.exploreGradient+q*a.quorumDecisionGradient+eH*a.unifiedEnemyHillsGradient+d*a.defenseGradient#+3*a.armyGradient

		orders = {}		
		def move(antLoc):
			#grad=gradients[gradType]
			sniff=[]
			for drxn in 'neswp':
				probeDest=a.destination(antLoc,drxn)
				sniff.append([self.unifiedGradient[probeDest],drxn,probeDest])
			sniff.sort(reverse=True)
			#logging.debug(sniff)
			for smellVal,drxn,dest in sniff:
				if drxn=='p' and smellVal>0.001:#dont pause if its an insignificant local optimum
					orders[antLoc]=antLoc
					return True
				if a.unoccupied(dest) and dest not in orders:
					a.issue_order((antLoc,drxn))
					orders[dest] = antLoc
					return True
			return False

		for antLoc in a.myAnts:
			move(antLoc)

		#logging.debug('turn '+ str(self.turn)+' '+str(a.time_remaining())+'\n')

            
if __name__ == '__main__':
    # psyco will speed up python a little, but is not needed
    try:
        import psyco
        psyco.full()
    except ImportError:
        pass
    
    try:
        # if run is passed a class with a do_turn method, it will do the work
        # this is not needed, in which case you will need to write your own
        # parsing function and your own game state class
        Ants.run(MyBot())
    except KeyboardInterrupt:
        print('ctrl-c, leaving ...')

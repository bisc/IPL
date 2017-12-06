#! /usr/bin/python
 
for loc in range(1, 9) + ['s']: # 1 to 8 and 's' location
    #print "s_%s_rot_e: process Task;" % loc

    for direction in range(0, 8): # from 0 (North) to 7 (Northwest)
        print "s_%s_rot_%d: process Task;"  % (loc, direction)
    
    print # newline



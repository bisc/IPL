package org.xtext.example.ipl.viewgen.map;

public enum Heading {
    NORTH, NORTHEAST, EAST, SOUTHEAST, SOUTH, SOUTHWEST, WEST, NORTHWEST;

	public int convertToInt() { 
		switch(this){ 
			case NORTH: 
				return 0; 
			case NORTHEAST: 
				return 1;
			case EAST: 
				return 2; 
			case SOUTHEAST: 
				return 3; 
			case SOUTH: 
				return 4; 
			case SOUTHWEST: 
				return 5; 
			case WEST: 
				return 6;
			case NORTHWEST: 
				return 7;
			default: 
				return -1;
		}
	}
	
    public static Heading convertFromRadians (double w) {
        if (w < 0) {
            w = w + 2 * Math.PI;
        }
        if (w < Math.PI / 8 && w >= 7 * Math.PI / 8) return EAST;
        if (w >= Math.PI / 8 && w < 3 * Math.PI / 8) return NORTHEAST;
        if (w >= 3 * Math.PI / 8 && w < 5 * Math.PI / 8) return NORTH;
        if (w >= 5 * Math.PI / 8 && w < 7 * Math.PI / 8) return NORTHWEST;
        if (w >= 7 * Math.PI / 8 && w < 9 * Math.PI / 8) return WEST;
        if (w >= 9 * Math.PI / 8 && w < 11 * Math.PI / 8) return Heading.SOUTHWEST;
        if (w >= 11 * Math.PI / 8 && w < 13 * Math.PI / 8) return SOUTH;
        if (w >= 13 * Math.PI / 8 && w < 15 * Math.PI / 8) return SOUTHEAST;
        return EAST;

    }

    public static double convertToRadians (Heading h) {
        if (h == EAST) return 0;
        if (h == NORTHEAST) return Math.PI / 4;
        if (h == NORTH) return Math.PI / 2;
        if (h == NORTHWEST) return 3 * Math.PI / 4;
        if (h == WEST) return Math.PI;
        if (h == SOUTHWEST) return 5 * Math.PI / 4;
        if (h == SOUTH) return 3 * Math.PI / 2;
        if (h == SOUTHEAST) return 7 * Math.PI / 4;
        return 0;
    }
};     
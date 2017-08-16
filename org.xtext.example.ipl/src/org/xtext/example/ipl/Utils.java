package org.xtext.example.ipl;

import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;

public class Utils {

	/**
	 * Run a shell command in the specified directory.  
	 * @param command command to be run
	 * @param dir the directory to run the command in. If dir is null, runs it in the current directory of the process.
	 * @return output of the command
	 */
	public static String executeShellCommand(String command, File dir) {

		StringBuffer output = new StringBuffer();
		System.out.println("Shell command:" + command);

		Process p;
		try {
			p = Runtime.getRuntime().exec(command, null, dir);
			p.waitFor();
			BufferedReader reader = 
					new BufferedReader(new InputStreamReader(p.getInputStream()));

			String line = "";			
			while ((line = reader.readLine())!= null) {
				output.append(line + "\n");
			}

		} catch (Exception e) {
			e.printStackTrace();
		}

		return output.toString();

	}
}

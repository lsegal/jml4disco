package org.jmlspecs.jml4.esc.distribution.configuration;

import java.util.HashMap;
import java.util.Map;
import java.util.Scanner;

import org.jmlspecs.jml4.esc.distribution.configuration.exceptions.FrontControllerException;

public class TestDriver {

	public static void main(String[] argv) {
		
		Scanner sc = new Scanner(System.in);
		
		while(true) {
			System.out.print("? ");
			String input = sc.nextLine();
			
			String[] inputs = input.split("\\s+",2);
			final String command;
			String[] arguments = {};
			if(inputs.length>0) {
				command = inputs[0];
			}
			else {
				command = "";
			}
			if(inputs.length>1) {
				arguments = inputs[1].split("\\s+");
			}
			
			try {
				CommandInput c = new CommandInput() {

					@Override
					public Object getAttribute(String name) {
						// TODO Auto-generated method stub
						return null;
					}

					@Override
					public String getCommandName() {
						return command;
					}

					@Override
					public Map getParameterMap() {
						return new HashMap<String, String>();
					}

					@Override
					public String getParameter(String name) {
						// TODO Auto-generated method stub
						return "";
					}

					@Override
					public void removeAttribute(String name) {
						
					}

					@Override
					public void setAttribute(String name, Object o) {
						
					}
					
				};
				DispatcherFrontController.main(c);
			} catch (FrontControllerException e) {
				// TODO Auto-generated catch block
				System.out.println(e.getMessage());
			}
		}
		
	}
	
}

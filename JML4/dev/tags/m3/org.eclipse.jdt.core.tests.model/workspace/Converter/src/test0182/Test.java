package test0182;
import java.util.*;
public class Test {
	public void foo() {
		int i= 10;
		if (/*]*/i < 10/*[*/)
			foo();
	}	
}
package org.jmlspecs.jml4.fspv;

public class NoSupportException extends RuntimeException {

	private static final long serialVersionUID = 6712870345103730994L;
	private static final String JDT_ELEMENT_IS_NOT_SUPPORTED = "JDT Element is not supported : \""; //$NON-NLS-1$
	private String message;

	public NoSupportException(String string) {
		super();
		this.message = JDT_ELEMENT_IS_NOT_SUPPORTED + string + "\""; //$NON-NLS-1$ 
	}
	
	public String toString() {
		return this.message;
	}
	
}

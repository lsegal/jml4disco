<%@ page language="java" contentType="text/html; charset=UTF-8"
    pageEncoding="UTF-8"%>
<p>
This page allows you to change how many concurrent prover processes there should be for various provers. <br>
For any prover that you wish to change, please fill the appropriate field with the number of processes you <br>
desire (an integer) and click submit.
</p>

<table>

<tr>
<th> Prover </th><th> &nbsp; </th>
</tr>
<tr>
<td> Isabelle </td><td> <form action='SetNumberOfProverProcesses' method='post' > <input name='MaxProcess' /> <input type='hidden' name='Prover-Name' value='Isabelle' /> <input type='submit' value='submit' /> </form> </td>
</tr>
<tr>
<td> Simplify </td><td> <form action='SetNumberOfProverProcesses' method='post' > <input name='MaxProcess' /> <input type='hidden' name='Prover-Name' value='Simplify' /> <input type='submit' value='submit' /> </form> </td>
</tr>

</table>
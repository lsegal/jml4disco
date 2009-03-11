<%@ page language="java" contentType="text/html; charset=UTF-8"
    pageEncoding="UTF-8"%>
This page will allow you to choose how many concurrent prover processes there should be for various provers:

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
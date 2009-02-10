<%@ page language="java" contentType="text/html; charset=UTF-8"
    pageEncoding="UTF-8"%>

<%@ include file="../servers.get.jsp" %>

This page will allow you to add servers:

<form method='POST' action='add'>
<label>Server url: </label>
<input name='server-url' />
<input type='submit' />
</form>
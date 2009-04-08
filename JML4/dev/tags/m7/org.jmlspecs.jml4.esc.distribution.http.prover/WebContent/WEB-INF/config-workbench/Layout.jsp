<%@ page language="java" contentType="text/html; charset=UTF-8"
    pageEncoding="UTF-8" import="java.io.PrintWriter,org.jmlspecs.jml4.esc.distribution.http.prover.config.servlets.Presentation"%>
<!DOCTYPE html PUBLIC -//W3C//DTD HTML 4.01 Transitional//EN http://www.w3.org/TR/html4/loose.dtd>
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
<title>JML4 Disco Configuration Interface | </title>
<meta name='keywords' content='' />
<meta name='description' content='' />
<style>
body { border: 0; background: #eee; }
#header { width: 100%; overflow-y: hidden; padding: 0px;height: 40px; }
#menu { width: 800px; float: left; font-family: sans-serif; padding-bottom: 10px; }
#menu ul { list-style: none; padding: 0; margin: 0; float: left; }
#menu li { float: left; display: block; } 
#menu a { display: block; padding: 20px; float: left; }
#menu a:link, #menu a:visited { color: #555; text-decoration: none; }
#menu a:hover { color: #fff; background-color: #af0a0a; padding: 20px; text-decoration: none; }
</style>
</head>
<body>
<div id='header'>
<div id='menu'>
	<ul>
		<li><a href='index.jsp' title=''>JML4 Disco - Server Config</a></li>
		<li><a href='SetNumberOfProverProcesses' >Configure Prover Processes</a></li>
	</ul>
</div>
</div>
<div>
<jsp:include page="<%= Presentation.getViewPath() %>" flush="false" />
</div>
</body>
</html>
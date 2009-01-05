<!DOCTYPE html
    PUBLIC "-//W3C//DTD XHTML 1.0 Strict//EN"
    "http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd">
<html xmlns="http://www.w3.org/1999/xhtml" lang="en" xml:lang="en">
<head>
 <title>#82: export-wiki-doc.rb - JML4 &#34;Disco&#34; - Trac</title><link rel="start" href="/trac/wiki" /><link rel="search" href="/trac/search" /><link rel="help" href="/trac/wiki/TracGuide" /><link rel="stylesheet" href="/trac/chrome/common/css/trac.css" type="text/css" /><link rel="stylesheet" href="/trac/chrome/common/css/code.css" type="text/css" /><link rel="icon" href="/favicon.ico" type="image/x-icon" /><link rel="shortcut icon" href="/favicon.ico" type="image/x-icon" /><link rel="up" href="/trac/ticket/82" title="Ticket #82" /><link rel="alternate" href="/trac/attachment/ticket/82/export-wiki-doc.rb?format=raw" title="Original Format" type="text/x-ruby; charset=iso-8859-15" /><style type="text/css">
</style>
 <script type="text/javascript" src="/trac/chrome/common/js/trac.js"></script>
</head>
<body>


<div id="banner">

<div id="header"><a id="logo" href="/trac"><img src="/images/jml4.png" alt="JML4" /></a><hr /></div>

<form id="search" action="/trac/search" method="get">
 <div>
  <label for="proj-search">Search:</label>
  <input type="text" id="proj-search" name="q" size="10" accesskey="f" value="" />
  <input type="submit" value="Search" />
  <input type="hidden" name="wiki" value="on" />
  <input type="hidden" name="changeset" value="on" />
  <input type="hidden" name="ticket" value="on" />
 </div>
</form>



<div id="metanav" class="nav"><ul><li class="first">logged in as l_sega</li><li><a href="/trac/logout">Logout</a></li><li><a href="/trac/settings">Settings</a></li><li><a accesskey="6" href="/trac/wiki/TracGuide">Help/Guide</a></li><li class="last"><a href="/trac/about">About Trac</a></li></ul></div>
</div>

<div id="mainnav" class="nav"><ul><li class="first"><a accesskey="1" href="/trac/wiki">Wiki</a></li><li><a accesskey="2" href="/trac/timeline">Timeline</a></li><li><a accesskey="3" href="/trac/roadmap">Roadmap</a></li><li><a href="/trac/browser">Browse Source</a></li><li><a href="/trac/report">View Tickets</a></li><li><a accesskey="7" href="/trac/newticket">New Ticket</a></li><li><a accesskey="4" href="/trac/search">Search</a></li><li class="last"><a href="/trac/admin">Admin</a></li></ul></div>
<div id="main">




<div id="ctxtnav" class="nav"></div>

<div id="content" class="attachment">


 <h1><a href="/trac/ticket/82">Ticket #82</a>: export-wiki-doc.rb</h1>
 <table id="info" summary="Description"><tbody><tr>
   <th scope="col">
    File export-wiki-doc.rb, 2.6 kB 
    (added by l_sega,  6 days ago)
   </th></tr><tr>
   <td class="message"><p>
Export wiki document script
</p>
</td>
  </tr>
 </tbody></table>
 <div id="preview">
   <table class="code"><thead><tr><th class="lineno">Line</th><th class="content">&nbsp;</th></tr></thead><tbody><tr><th id="L1"><a href="#L1">1</a></th>
<td>require 'rubygems'</td>
</tr><tr><th id="L2"><a href="#L2">2</a></th>
<td>require 'net/https'</td>
</tr><tr><th id="L3"><a href="#L3">3</a></th>
<td>require 'hpricot'</td>
</tr><tr><th id="L4"><a href="#L4">4</a></th>
<td>require 'fileutils'</td>
</tr><tr><th id="L5"><a href="#L5">5</a></th>
<td></td>
</tr><tr><th id="L6"><a href="#L6">6</a></th>
<td># wiki documents to process</td>
</tr><tr><th id="L7"><a href="#L7">7</a></th>
<td>wikidocs = { </td>
</tr><tr><th id="L8"><a href="#L8">8</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; 'VisionDocument' =&gt; 'mgmt'</td>
</tr><tr><th id="L9"><a href="#L9">9</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp;}</td>
</tr><tr><th id="L10"><a href="#L10">10</a></th>
<td>username = 'USERNAME'</td>
</tr><tr><th id="L11"><a href="#L11">11</a></th>
<td>password = 'PASSWORD'</td>
</tr><tr><th id="L12"><a href="#L12">12</a></th>
<td>base_url = &#34;https://group0j.stu01.encs.concordia.ca:9443/trac/wiki/&#34;</td>
</tr><tr><th id="L13"><a href="#L13">13</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp;</td>
</tr><tr><th id="L14"><a href="#L14">14</a></th>
<td>def process(document_name, category)</td>
</tr><tr><th id="L15"><a href="#L15">15</a></th>
<td></td>
</tr><tr><th id="L16"><a href="#L16">16</a></th>
<td>&nbsp; filename = category + '/' + document_name.gsub(/([a-z])([A-Z])/,'\1-\2').downcase + '.html'</td>
</tr><tr><th id="L17"><a href="#L17">17</a></th>
<td></td>
</tr><tr><th id="L18"><a href="#L18">18</a></th>
<td>&nbsp; # common HTML elements to remove (expressed with css selectors)</td>
</tr><tr><th id="L19"><a href="#L19">19</a></th>
<td>&nbsp; elements_to_remove = [&#34;html &gt; head &gt; link&#34;,</td>
</tr><tr><th id="L20"><a href="#L20">20</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &#34;html &gt; head &gt; style&#34;,</td>
</tr><tr><th id="L21"><a href="#L21">21</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &#34;html &gt; head &gt; script&#34;,</td>
</tr><tr><th id="L22"><a href="#L22">22</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &#34;html &gt; body &gt; script&#34;,</td>
</tr><tr><th id="L23"><a href="#L23">23</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &#34;div#banner&#34;,</td>
</tr><tr><th id="L24"><a href="#L24">24</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &#34;div#header&#34;,</td>
</tr><tr><th id="L25"><a href="#L25">25</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &#34;div#search&#34;,</td>
</tr><tr><th id="L26"><a href="#L26">26</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &#34;div#ctxtnav&#34;,</td>
</tr><tr><th id="L27"><a href="#L27">27</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &#34;div#metanav&#34;,</td>
</tr><tr><th id="L28"><a href="#L28">28</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &#34;div#mainnav&#34;,</td>
</tr><tr><th id="L29"><a href="#L29">29</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &#34;div.buttons&#34;,</td>
</tr><tr><th id="L30"><a href="#L30">30</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &#34;div#altlinks&#34;,</td>
</tr><tr><th id="L31"><a href="#L31">31</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &#34;div#footer&#34;,</td>
</tr><tr><th id="L32"><a href="#L32">32</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &#34;h3#tkt-changes-hdr&#34;,</td>
</tr><tr><th id="L33"><a href="#L33">33</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &#34;ul.tkt-chg-list&#34;]</td>
</tr><tr><th id="L34"><a href="#L34">34</a></th>
<td></td>
</tr><tr><th id="L35"><a href="#L35">35</a></th>
<td>&nbsp; # process html and write file</td>
</tr><tr><th id="L36"><a href="#L36">36</a></th>
<td>&nbsp; begin</td>
</tr><tr><th id="L37"><a href="#L37">37</a></th>
<td>&nbsp; &nbsp; # load the wiki page</td>
</tr><tr><th id="L38"><a href="#L38">38</a></th>
<td>&nbsp; &nbsp; uri = URI.parse(base_url + document_name)</td>
</tr><tr><th id="L39"><a href="#L39">39</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; req = Net::HTTP::Get.new(uri.path)</td>
</tr><tr><th id="L40"><a href="#L40">40</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; req.basic_auth(username, password)</td>
</tr><tr><th id="L41"><a href="#L41">41</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; http = Net::HTTP.new(uri.host, uri.port)</td>
</tr><tr><th id="L42"><a href="#L42">42</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; http.use_ssl = true</td>
</tr><tr><th id="L43"><a href="#L43">43</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; http.verify_mode = OpenSSL::SSL::VERIFY_NONE</td>
</tr><tr><th id="L44"><a href="#L44">44</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; http.enable_post_connection_check = false</td>
</tr><tr><th id="L45"><a href="#L45">45</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; response = http.request(req)</td>
</tr><tr><th id="L46"><a href="#L46">46</a></th>
<td></td>
</tr><tr><th id="L47"><a href="#L47">47</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; doc = Hpricot(response.body)</td>
</tr><tr><th id="L48"><a href="#L48">48</a></th>
<td>&nbsp; </td>
</tr><tr><th id="L49"><a href="#L49">49</a></th>
<td>&nbsp; &nbsp; # search for each element and remove it from the doc</td>
</tr><tr><th id="L50"><a href="#L50">50</a></th>
<td>&nbsp; &nbsp; elements_to_remove.each { |e| doc.search(e).remove }</td>
</tr><tr><th id="L51"><a href="#L51">51</a></th>
<td></td>
</tr><tr><th id="L52"><a href="#L52">52</a></th>
<td>&nbsp; &nbsp; # set title</td>
</tr><tr><th id="L53"><a href="#L53">53</a></th>
<td>&nbsp; &nbsp; doc.search(&#34;html &gt; head&#34;).at(&#34;title&#34;).inner_html = &#34;markr - &#34; + document_name.gsub(/([a-z])([A-Z])/,'\1 \2')</td>
</tr><tr><th id="L54"><a href="#L54">54</a></th>
<td>&nbsp; </td>
</tr><tr><th id="L55"><a href="#L55">55</a></th>
<td>&nbsp; &nbsp; # add link to css</td>
</tr><tr><th id="L56"><a href="#L56">56</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; updir = &#34;../&#34; * category.split(/\//).size</td>
</tr><tr><th id="L57"><a href="#L57">57</a></th>
<td>&nbsp; &nbsp; css = %Q(&lt;link rel=&#34;stylesheet&#34; type=&#34;text/css&#34; href=&#34;#{updir}style.css&#34; /&gt;)</td>
</tr><tr><th id="L58"><a href="#L58">58</a></th>
<td>&nbsp; &nbsp; doc.search(&#34;html &gt; head&#34;).append(css)</td>
</tr><tr><th id="L59"><a href="#L59">59</a></th>
<td></td>
</tr><tr><th id="L60"><a href="#L60">60</a></th>
<td>&nbsp; &nbsp; # give toc's parent ol a class</td>
</tr><tr><th id="L61"><a href="#L61">61</a></th>
<td>&nbsp; &nbsp; ol = doc.search(&#34;html &gt; body &gt; div.wiki-toc &gt; ol&#34;).first</td>
</tr><tr><th id="L62"><a href="#L62">62</a></th>
<td>&nbsp; &nbsp; ol.attributes['class'] = 'top-most' unless ol.nil?</td>
</tr><tr><th id="L63"><a href="#L63">63</a></th>
<td>&nbsp; &nbsp; </td>
</tr><tr><th id="L64"><a href="#L64">64</a></th>
<td>&nbsp; &nbsp; # change the toc's li's class names</td>
</tr><tr><th id="L65"><a href="#L65">65</a></th>
<td>&nbsp; &nbsp; doc.search(&#34;html &gt; body &gt; div.wiki-toc &gt; ol&#34;).search(&#34;li.active&#34;).set(:class =&gt; 'toc') rescue nil</td>
</tr><tr><th id="L66"><a href="#L66">66</a></th>
<td>&nbsp; &nbsp; &nbsp; &nbsp; </td>
</tr><tr><th id="L67"><a href="#L67">67</a></th>
<td>&nbsp; &nbsp; # create category directory if it does not exist, and write HTML to file</td>
</tr><tr><th id="L68"><a href="#L68">68</a></th>
<td>&nbsp; &nbsp; FileUtils.mkdir_p(category) rescue nil</td>
</tr><tr><th id="L69"><a href="#L69">69</a></th>
<td>&nbsp; &nbsp; File.open(filename, &#34;w&#34;) { |f| f.write(doc.to_html); f.close }</td>
</tr><tr><th id="L70"><a href="#L70">70</a></th>
<td>&nbsp; &nbsp; print &#34;wrote #{filename}... &#34;</td>
</tr><tr><th id="L71"><a href="#L71">71</a></th>
<td>&nbsp; rescue StandardError =&gt; bang</td>
</tr><tr><th id="L72"><a href="#L72">72</a></th>
<td>&nbsp; &nbsp; print &#34;(Oops! &#34; + bang + &#34;) &#34;</td>
</tr><tr><th id="L73"><a href="#L73">73</a></th>
<td>&nbsp; end</td>
</tr><tr><th id="L74"><a href="#L74">74</a></th>
<td>&nbsp; </td>
</tr><tr><th id="L75"><a href="#L75">75</a></th>
<td>end</td>
</tr><tr><th id="L76"><a href="#L76">76</a></th>
<td></td>
</tr><tr><th id="L77"><a href="#L77">77</a></th>
<td>wikidocs.each do |name, category|</td>
</tr><tr><th id="L78"><a href="#L78">78</a></th>
<td>&nbsp; print &#34;Exporting \&#34;&#34; + name + &#34;\&#34;... &#34;</td>
</tr><tr><th id="L79"><a href="#L79">79</a></th>
<td>&nbsp; process(name, category)</td>
</tr><tr><th id="L80"><a href="#L80">80</a></th>
<td>&nbsp; puts &#34;done.&#34;</td>
</tr><tr><th id="L81"><a href="#L81">81</a></th>
<td>end</td>
</tr></tbody></table>
 </div>
 <div class="buttons">
  <form method="get" action=""><div id="delete">
   <input type="hidden" name="action" value="delete" />
   <input type="submit" value="Delete attachment" />
  </div></form>
 </div>


</div>
<script type="text/javascript">searchHighlight()</script>
<div id="altlinks"><h3>Download in other formats:</h3><ul><li class="first last"><a href="/trac/attachment/ticket/82/export-wiki-doc.rb?format=raw">Original Format</a></li></ul></div>

</div>

<div id="footer">
 <hr />
 <a id="tracpowered" href="http://trac.edgewall.org/"><img src="/trac/chrome/common/trac_logo_mini.png" height="30" width="107"
   alt="Trac Powered"/></a>
 <p class="left">
  Powered by <a href="/trac/about"><strong>Trac 0.10.4</strong></a><br />
  By <a href="http://www.edgewall.org/">Edgewall Software</a>.
 </p>
 <p class="right">
  SOEN490, Trac's got your backs!
 </p>
</div>



 </body>
</html>


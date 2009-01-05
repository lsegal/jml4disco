require 'rubygems'
require 'net/https'
require 'hpricot'
require 'fileutils'

# wiki documents to process
wikidocs = { 
				'VisionDocument' => 'mgmt'
           }
username = 'USERNAME'
password = 'PASSWORD'
base_url = "https://group0j.stu01.encs.concordia.ca:9443/trac/wiki/"
             
def process(document_name, category)

  filename = category + '/' + document_name.gsub(/([a-z])([A-Z])/,'\1-\2').downcase + '.html'

  # common HTML elements to remove (expressed with css selectors)
  elements_to_remove = ["html > head > link",
                        "html > head > style",
                        "html > head > script",
                        "html > body > script",
                        "div#banner",
                        "div#header",
                        "div#search",
                        "div#ctxtnav",
                        "div#metanav",
                        "div#mainnav",
                        "div.buttons",
                        "div#altlinks",
                        "div#footer",
                        "h3#tkt-changes-hdr",
                        "ul.tkt-chg-list"]

  # process html and write file
  begin
    # load the wiki page
    uri = URI.parse(base_url + document_name)
	req = Net::HTTP::Get.new(uri.path)
	req.basic_auth(username, password)
	http = Net::HTTP.new(uri.host, uri.port)
	http.use_ssl = true
	http.verify_mode = OpenSSL::SSL::VERIFY_NONE
	http.enable_post_connection_check = false
	response = http.request(req)

	doc = Hpricot(response.body)
  
    # search for each element and remove it from the doc
    elements_to_remove.each { |e| doc.search(e).remove }

    # set title
    doc.search("html > head").at("title").inner_html = "markr - " + document_name.gsub(/([a-z])([A-Z])/,'\1 \2')
  
    # add link to css
	updir = "../" * category.split(/\//).size
    css = %Q(<link rel="stylesheet" type="text/css" href="#{updir}style.css" />)
    doc.search("html > head").append(css)

    # give toc's parent ol a class
    ol = doc.search("html > body > div.wiki-toc > ol").first
    ol.attributes['class'] = 'top-most' unless ol.nil?
    
    # change the toc's li's class names
    doc.search("html > body > div.wiki-toc > ol").search("li.active").set(:class => 'toc') rescue nil
        
    # create category directory if it does not exist, and write HTML to file
    FileUtils.mkdir_p(category) rescue nil
    File.open(filename, "w") { |f| f.write(doc.to_html); f.close }
    print "wrote #{filename}... "
  rescue StandardError => bang
    print "(Oops! " + bang + ") "
  end
  
end

wikidocs.each do |name, category|
  print "Exporting \"" + name + "\"... "
  process(name, category)
  puts "done."
end


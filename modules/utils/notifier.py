import smtplib

def sendEmail(configuration):
	status = True

 	sender = configuration["sender"]
 	recepient = configuration["receipient"]
	smtp_server = configuration["smtpserver"]
	smtp_port = configuration["port"]
    password = configuration["password"]
	session = smtplib.SMTP(smtp_server, smtp_port)
	try:
		session.ehlo()
		session.starttls()
		session.ehlo
		session.login(sender, password=)
		headers = ["From: " + sender,
		"Subject: Your experiment is done",
		"To: " + recepient,
		"MIME-Version: 1.0",
		"Content-Type: text/html"]
		headers = "\r\n".join(headers)
		session.sendmail(sender, recepient, headers + "\r\n\r\n" +  message)
	except Exception, e:
		status = False
		print e
	finally:
		session.quit()

	return status

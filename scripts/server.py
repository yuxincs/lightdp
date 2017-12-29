import tornado.ioloop
import tornado.web
import subprocess


class CompileHandler(tornado.web.RequestHandler):
    def post(self):
        res = subprocess.run(
            ['python', '-m', 'lightdp', '/dev/stdin', '--json', '/dev/stdout', '-o', '/dev/null'],
            stdout=subprocess.PIPE,
            input=str(self.request.body, 'utf-8'),
            encoding='utf-8')
        self.add_header('Access-Control-Allow-Origin', '*')
        self.write(res.stdout)


def main():
    app = tornado.web.Application([
        (r'/compile', CompileHandler),
    ])
    app.listen(8080)
    tornado.ioloop.IOLoop.current().start()


if __name__ == '__main__':
    main()
